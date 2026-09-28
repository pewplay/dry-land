/*
 * Dry Land
 * Original game: "Dutch Dredge" by Rick van Mook, js13kGames 2015 (MIT licence, see LICENSE).
 * Rebuilt for PewPlay: canvas renderer, responsive layout, touch and keyboard controls.
 *
 * The rules are the original ones: every tile of the polder has a land side and a
 * water side. Clicking a tile flips it together with its four direct neighbours.
 * A level is cleared when every tile shows its land side.
 */
(function () {
  'use strict';

  var GAME_ID = 'dry-land';

  // ------------------------------------------------------------------
  // Levels (from the original game). 6x6 grid, read row by row:
  // ' ' = no tile, '0' = land, '1' = water.
  // After these, levels are generated.
  // ------------------------------------------------------------------
  var LEVELS = [
    '      ' +
    ' 1111 ' +
    ' 1111 ' +
    ' 1111 ' +
    ' 1111 ' +
    '      ',

    '      ' +
    ' 0111 ' +
    ' 1111 ' +
    ' 0100 ' +
    '      ' +
    '      ',

    '      ' +
    ' 0001 ' +
    ' 0010 ' +
    ' 0100 ' +
    ' 1000 ' +
    '      ',

    '      ' +
    ' 1100 ' +
    ' 1110 ' +
    ' 0111 ' +
    ' 0011 ' +
    '      ',

    '010010' +
    '111111' +
    '010010' +
    '010010' +
    '111111' +
    '010010',

    '111111' +
    '110010' +
    '110001' +
    '100011' +
    '010011' +
    '111111',

    '100001' +
    '011110' +
    '010010' +
    '010010' +
    '011110' +
    '100001',

    '101110' +
    '011001' +
    '011101' +
    '010111' +
    '111111' +
    '010010'
  ];

  var N = 6;                // grid size
  var CELLS = N * N;
  var TILE = 60;            // tile size in world units
  var DIRT = 7;             // thickness of the land slab
  var WATER = 20;           // height of the water box
  var LIFT = 12;            // how far a hovered tile rises

  // Camera. Landscape screens use the original isometric-style view (45 degree turn,
  // 25 degree elevation, as in the original CSS). Tall portrait screens turn the polder
  // to face the player, which makes the tiles much larger on a phone.
  var cam = { yaw: 0, elev: 0, sinY: 0, cosY: 0, sinE: 0, cosE: 0, view: [0, 0, 1] };
  function setCamera(yawDeg, elevDeg) {
    cam.yaw = yawDeg; cam.elev = elevDeg;
    cam.sinY = Math.sin(yawDeg * Math.PI / 180); cam.cosY = Math.cos(yawDeg * Math.PI / 180);
    cam.sinE = Math.sin(elevDeg * Math.PI / 180); cam.cosE = Math.cos(elevDeg * Math.PI / 180);
    // unit vector pointing from the board towards the viewer
    cam.view = [cam.sinY * cam.cosE, cam.cosY * cam.cosE, cam.sinE];
  }
  setCamera(45, 25);
  var PORTRAIT_YAW = 0, PORTRAIT_ELEV = 48;

  var COLORS = {
    sand: '#f8e4b0',
    grass: '#00cc00',
    grassLine: '#006800',
    dirt: '#ce9c5a',
    dirtLine: '#7b6b18',
    water: '176,240,248',
    waterLine: '#70c8f0',
    waterFloor: '#b0f0f8'
  };

  // ------------------------------------------------------------------
  // Storage (every key is prefixed with the game id)
  // ------------------------------------------------------------------
  var store = {
    get: function (key, fallback) {
      try {
        var v = localStorage.getItem(GAME_ID + ':' + key);
        return v === null ? fallback : JSON.parse(v);
      } catch (e) { return fallback; }
    },
    set: function (key, value) {
      try { localStorage.setItem(GAME_ID + ':' + key, JSON.stringify(value)); } catch (e) { /* ignore */ }
    }
  };

  // ------------------------------------------------------------------
  // Sound: the two original samples, played through Web Audio.
  // The AudioContext is only created after the first user gesture.
  // ------------------------------------------------------------------
  var audio = {
    ctx: null,
    buffers: {},
    muted: !!store.get('muted', false),
    lastHover: 0,

    unlock: function () {
      if (this.ctx) {
        if (this.ctx.state === 'suspended') this.ctx.resume();
        return;
      }
      var AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return;
      this.ctx = new AC();
      var self = this;
      ['click', 'hover'].forEach(function (name) {
        fetch(name + '.mp3')
          .then(function (r) { return r.arrayBuffer(); })
          .then(function (data) {
            return new Promise(function (resolve, reject) { self.ctx.decodeAudioData(data, resolve, reject); });
          })
          .then(function (buf) { self.buffers[name] = buf; })
          .catch(function () { /* sound is optional */ });
      });
    },

    play: function (name, volume) {
      if (this.muted || !this.ctx || !this.buffers[name] || this.ctx.state !== 'running') return;
      if (name === 'hover') {
        var now = this.ctx.currentTime;
        if (now - this.lastHover < 0.025) return;   // avoid machine-gun stacking
        this.lastHover = now;
      }
      var src = this.ctx.createBufferSource();
      var gain = this.ctx.createGain();
      gain.gain.value = volume === undefined ? 0.8 : volume;
      src.buffer = this.buffers[name];
      src.connect(gain);
      gain.connect(this.ctx.destination);
      src.start();
    }
  };

  // ------------------------------------------------------------------
  // Puzzle maths: flip patterns, solver (Gaussian elimination over GF(2))
  // ------------------------------------------------------------------
  function neighbours(k) {
    var x = k % N, y = (k / N) | 0, out = [k];
    if (x > 0) out.push(k - 1);
    if (x < N - 1) out.push(k + 1);
    if (y > 0) out.push(k - N);
    if (y < N - 1) out.push(k + N);
    return out;
  }

  /**
   * Minimal set of presses that turns every present tile into land.
   * @param {boolean[]} present
   * @param {number[]} water  1 = water, 0 = land
   * @returns {number[]|null} list of tile indices, or null if unsolvable
   */
  function solve(present, water) {
    var cells = [], idx = {}, i, j, c;
    for (i = 0; i < CELLS; i++) if (present[i]) { idx[i] = cells.length; cells.push(i); }
    var n = cells.length;
    var rows = cells.map(function (k) {
      var r = new Array(n + 1).fill(0);
      neighbours(k).forEach(function (m) { if (idx[m] !== undefined) r[idx[m]] = 1; });
      r[n] = water[k] ? 1 : 0;
      return r;
    });
    var where = new Array(n).fill(-1), rank = 0, tmp;
    for (c = 0; c < n && rank < n; c++) {
      var p = -1;
      for (i = rank; i < n; i++) if (rows[i][c]) { p = i; break; }
      if (p < 0) continue;
      tmp = rows[rank]; rows[rank] = rows[p]; rows[p] = tmp;
      for (i = 0; i < n; i++) {
        if (i !== rank && rows[i][c]) for (j = c; j <= n; j++) rows[i][j] ^= rows[rank][j];
      }
      where[c] = rank++;
    }
    for (i = rank; i < n; i++) if (rows[i][n]) return null;
    var free = [];
    for (c = 0; c < n; c++) if (where[c] < 0) free.push(c);
    var best = null;
    for (var m = 0; m < (1 << free.length); m++) {
      var x = new Array(n).fill(0), count = 0;
      free.forEach(function (fc, b) { x[fc] = (m >> b) & 1; });
      for (c = 0; c < n; c++) {
        if (where[c] < 0) continue;
        var row = rows[where[c]], v = row[n];
        for (j = 0; j < free.length; j++) if (row[free[j]] && x[free[j]]) v ^= 1;
        x[c] = v;
      }
      for (c = 0; c < n; c++) count += x[c];
      if (!best || count < best.length) {
        best = [];
        for (c = 0; c < n; c++) if (x[c]) best.push(cells[c]);
      }
    }
    return best;
  }

  // Small seeded random generator, so generated level N is always the same puzzle.
  function rng(seed) {
    return function () {
      seed |= 0; seed = seed + 0x6D2B79F5 | 0;
      var t = Math.imul(seed ^ seed >>> 15, 1 | seed);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }

  /** Level definition string for level number `n` (1-based). */
  function levelString(n) {
    if (n <= LEVELS.length) return LEVELS[n - 1];
    // Generated levels: a full 6x6 polder scrambled with a growing number of presses.
    // The 6x6 grid is always solvable, so these are fair puzzles.
    var rand = rng(n * 7919 + 13);
    var presses = Math.min(5 + Math.floor((n - LEVELS.length - 1) / 2), 13);
    for (;;) {
      var water = new Array(CELLS).fill(0), chosen = {}, count = 0;
      while (count < presses) {
        var k = Math.floor(rand() * CELLS);
        if (chosen[k]) continue;
        chosen[k] = 1; count++;
        neighbours(k).forEach(function (m) { water[m] ^= 1; });
      }
      if (water.indexOf(1) >= 0) return water.join('');
    }
  }

  // ------------------------------------------------------------------
  // Tweens
  // ------------------------------------------------------------------
  var now = 0; // game clock in seconds (only runs while the page is visible)

  function Tween(v) { this.from = v; this.to = v; this.t0 = 0; this.dur = 0.3; this.delay = 0; }
  Tween.prototype.value = function () {
    var t = (now - this.t0 - this.delay) / this.dur;
    if (t <= 0) return this.from;
    if (t >= 1) return this.to;
    return this.from + (this.to - this.from) * (t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2);
  };
  Tween.prototype.set = function (to, dur, delay) {
    var current = this.value();
    this.from = current;
    this.to = to;
    this.t0 = now;
    this.dur = dur === undefined ? 0.3 : dur;
    this.delay = delay || 0;
  };
  Tween.prototype.jump = function (v) { this.from = this.to = v; this.t0 = now; this.delay = 0; };
  Tween.prototype.done = function () { return now >= this.t0 + this.delay + this.dur; };

  // ------------------------------------------------------------------
  // Game state
  // ------------------------------------------------------------------
  var tiles = [];
  for (var t = 0; t < CELLS; t++) {
    tiles.push({
      k: t,
      col: t % N,
      row: (t / N) | 0,
      present: false,
      water: 0,
      rot: new Tween(0),       // 0 = land up, PI = water up
      lift: new Tween(1),
      alpha: new Tween(0)
    });
  }

  var game = {
    state: 'menu',            // 'menu' | 'play' | 'clearing'
    level: Math.max(1, store.get('level', 1) | 0),
    start: '',
    moves: 0,
    par: 0,
    hintUsed: false,
    hint: -1,
    hover: -1,                // tile under the mouse / finger / keyboard cursor
    pressed: -1,
    cursorVisible: false,
    readyAt: 0,
    events: [],               // scheduled callbacks [time, fn]
    stuckShown: false
  };

  function schedule(delay, fn) { game.events.push([now + delay, fn]); }

  function presentMask() { return tiles.map(function (tl) { return tl.present; }); }
  function waterMask() { return tiles.map(function (tl) { return tl.water; }); }

  function loadLevel(n, isReset) {
    game.level = n;
    game.events = [];
    game.moves = 0;
    game.hint = -1;
    game.stuckShown = false;
    if (!isReset) {
      game.start = levelString(n);
      game.hintUsed = false;
      store.set('level', n);
    }
    var s = game.start, lastDelay = 0;
    tiles.forEach(function (tl, i) {
      var ch = s[i];
      var wasPresent = tl.present;
      tl.present = ch !== ' ';
      if (!tl.present) {
        tl.water = 0;
        tl.alpha.set(0, 0.2);
        return;
      }
      tl.water = +ch;
      if (isReset && wasPresent) {
        tl.rot.set(tl.water ? Math.PI : 0, 0.45);
        return;
      }
      // Tiles drop in one after another, like in the original.
      var delay = 0.3 + i * 0.02;
      lastDelay = delay;
      tl.rot.jump(tl.water ? Math.PI : 0);
      tl.lift.jump(1);
      tl.alpha.jump(0);
      tl.alpha.set(1, 0.3, delay);
      tl.lift.set(0, 0.3, delay);
      schedule(delay, function () { audio.play('hover', 0.35); });
    });
    game.readyAt = now + (isReset ? 0.2 : Math.min(lastDelay + 0.15, 0.4));
    game.par = (solve(presentMask(), waterMask()) || []).length;
    updateLift();
    updateHud();
    fitBoard();
  }

  function isSolved() {
    for (var i = 0; i < CELLS; i++) if (tiles[i].present && tiles[i].water) return false;
    return true;
  }

  function press(k) {
    if (game.state !== 'play' || now < game.readyAt || k < 0 || !tiles[k].present) return;
    neighbours(k).forEach(function (m) {
      var tl = tiles[m];
      if (!tl.present) return;
      tl.water ^= 1;
      tl.rot.set(tl.water ? Math.PI : 0, 0.4);
    });
    game.moves++;
    game.hint = -1;
    audio.play('click', 0.9);
    hideMessage();
    if (isSolved()) {
      celebrate();
    } else if (!game.stuckShown && game.moves >= Math.max(8, game.par * 2 + 4)) {
      game.stuckShown = true;
      showMessage('Stuck? Reset the level or ask for a hint', 5);
      resetBtn.classList.add('nudge');
    }
    updateHud();
  }

  function celebrate() {
    game.state = 'clearing';
    game.hover = -1;
    game.pressed = -1;
    updateLift();
    resetBtn.classList.remove('nudge');

    var perfect = game.moves <= game.par && !game.hintUsed;
    bannerTitle.textContent = 'Level ' + game.level + ' cleared';
    bannerSub.textContent = game.moves + (game.moves === 1 ? ' move' : ' moves') + ' · par ' + game.par;
    bannerPerfect.textContent = perfect ? 'Perfect!' : (game.hintUsed ? 'Try it without hints next time' : '');
    schedule(0.35, function () { banner.classList.add('show'); });

    // Lift every tile in turn, then lower and fade it out (the original "celebrate").
    var last = 0;
    tiles.forEach(function (tl, i) {
      if (!tl.present) return;
      var d = 0.45 + i * 0.02;
      last = d;
      tl.lift.set(1, 0.3, d);
      schedule(d, function () { audio.play('hover', 0.4); });
      schedule(d + 0.3, function () {
        tl.lift.set(0, 0.3);
        tl.alpha.set(0, 0.35);
      });
    });
    schedule(last + 1.1, function () { banner.classList.remove('show'); });
    schedule(last + 1.35, function () {
      game.state = 'play';
      loadLevel(game.level + 1);
    });
  }

  function resetLevel() {
    if (game.state !== 'play') return;
    resetBtn.classList.remove('nudge');
    hideMessage();
    loadLevel(game.level, true);
  }

  function showHint() {
    if (game.state !== 'play' || now < game.readyAt) return;
    var sol = solve(presentMask(), waterMask());
    if (!sol || !sol.length) return;
    // Prefer the solution tile closest to where the player is looking.
    var ref = game.hover >= 0 ? game.hover : sol[0];
    sol.sort(function (a, b) {
      return dist(a, ref) - dist(b, ref) || a - b;
    });
    game.hint = sol[0];
    game.hintUsed = true;
    game.hintAt = now;
    showMessage(sol.length === 1 ? 'One more move!' : sol.length + ' moves to go', 3);
  }

  function dist(a, b) {
    return Math.abs(a % N - b % N) + Math.abs(((a / N) | 0) - ((b / N) | 0));
  }

  // Raise the hovered tile and its neighbours (the original hover preview).
  function updateLift() {
    var raised = {};
    if (game.state === 'play' && game.hover >= 0 && tiles[game.hover].present) {
      neighbours(game.hover).forEach(function (m) { raised[m] = true; });
    }
    if (game.state === 'clearing') return;
    tiles.forEach(function (tl, i) {
      if (!tl.present || now < game.readyAt - 0.1) return;
      var target = raised[i] ? 1 : 0;
      if (tl.lift.to !== target) tl.lift.set(target, 0.25);
    });
  }

  // ------------------------------------------------------------------
  // Rendering
  // ------------------------------------------------------------------
  var canvas = document.getElementById('board');
  var ctx = canvas.getContext('2d');
  var view = { w: 0, h: 0, dpr: 1, scale: 1, ox: 0, oy: 0 };

  function project(x, y, z) {
    var d = x * cam.sinY + y * cam.cosY;
    return [view.ox + (x * cam.cosY - y * cam.sinY) * view.scale, view.oy + (d * cam.sinE - z * cam.cosE) * view.scale];
  }
  function depth(x, y, z) { return (x * cam.sinY + y * cam.cosY) * cam.cosE + z * cam.sinE; }
  function tileDepth(tl) { var c = tileCenter(tl); return depth(c[0], c[1], 0); }

  function tileCenter(tl) {
    return [(tl.col - (N - 1) / 2) * TILE, (tl.row - (N - 1) / 2) * TILE];
  }

  // Build the six faces of an axis-aligned box in tile space.
  function boxFaces(x0, x1, y0, y1, z0, z1) {
    var P = function (x, y, z) { return [x, y, z]; };
    return [
      { key: 'top', n: [0, 0, 1], v: [P(x0, y0, z1), P(x1, y0, z1), P(x1, y1, z1), P(x0, y1, z1)] },
      { key: 'bottom', n: [0, 0, -1], v: [P(x0, y0, z0), P(x0, y1, z0), P(x1, y1, z0), P(x1, y0, z0)] },
      { key: 'px', n: [1, 0, 0], v: [P(x1, y0, z0), P(x1, y1, z0), P(x1, y1, z1), P(x1, y0, z1)] },
      { key: 'nx', n: [-1, 0, 0], v: [P(x0, y0, z0), P(x0, y0, z1), P(x0, y1, z1), P(x0, y1, z0)] },
      { key: 'py', n: [0, 1, 0], v: [P(x0, y1, z0), P(x0, y1, z1), P(x1, y1, z1), P(x1, y1, z0)] },
      { key: 'ny', n: [0, -1, 0], v: [P(x0, y0, z0), P(x1, y0, z0), P(x1, y0, z1), P(x0, y0, z1)] }
    ];
  }

  var H = TILE / 2;

  // Rotate a tile-space point about the X axis and move it into the world.
  function place(p, cos, sin, cx, cy, cz) {
    return [cx + p[0], cy + p[1] * cos - p[2] * sin, cz + p[1] * sin + p[2] * cos];
  }

  function drawPoly(pts, fill, stroke, lw) {
    ctx.beginPath();
    for (var i = 0; i < pts.length; i++) {
      var s = project(pts[i][0], pts[i][1], pts[i][2]);
      if (i) ctx.lineTo(s[0], s[1]); else ctx.moveTo(s[0], s[1]);
    }
    ctx.closePath();
    ctx.fillStyle = fill;
    ctx.fill();
    if (stroke) {
      ctx.strokeStyle = stroke;
      ctx.lineWidth = lw;
      ctx.stroke();
    }
  }

  function faceDepth(pts) {
    var d = 0;
    for (var i = 0; i < pts.length; i++) d += depth(pts[i][0], pts[i][1], pts[i][2]);
    return d / pts.length;
  }

  function shade(hex, f) {
    var n = parseInt(hex.slice(1), 16);
    var r = Math.round(((n >> 16) & 255) * f), g = Math.round(((n >> 8) & 255) * f), b = Math.round((n & 255) * f);
    return 'rgb(' + Math.min(255, r) + ',' + Math.min(255, g) + ',' + Math.min(255, b) + ')';
  }

  function drawTile(tl) {
    var alpha = tl.alpha.value();
    if (alpha <= 0.001) return;
    var c = tileCenter(tl);
    var theta = tl.rot.value();
    var cos = Math.cos(theta), sin = Math.sin(theta);
    var lift = tl.lift.value() * LIFT + Math.sin(theta) * 14; // small hop while flipping
    var cz = lift;
    var lw = Math.max(1, view.scale * 0.75);

    // Water level pulses gently, row by row, like the original animation.
    var wh = WATER + Math.sin(now * (2 * Math.PI / 1.5) - tl.col * 0.63) * 1.6;
    var waterVis = (1 - cos) / 2;   // the water only shows once its side swings up

    var dirt = boxFaces(-H, H, -H, H, 0, DIRT);
    var water = boxFaces(-H + 0.6, H - 0.6, -H + 0.6, H - 0.6, -wh, 0);

    function transform(face) {
      var pts = face.v.map(function (p) { return place(p, cos, sin, c[0], c[1], cz); });
      var n = face.n;
      var nn = [n[0], n[1] * cos - n[2] * sin, n[1] * sin + n[2] * cos];
      return { key: face.key, pts: pts, n: nn, facing: nn[0] * cam.view[0] + nn[1] * cam.view[1] + nn[2] * cam.view[2] };
    }

    var dirtFaces = dirt.map(transform);
    var waterFaces = water.filter(function (f) { return f.key !== 'top'; }).map(transform);

    function drawDirt() {
      ctx.globalAlpha = alpha;
      dirtFaces
        .filter(function (f) { return f.facing > 0.001; })
        .forEach(function (f) {
          if (f.key === 'top') {
            drawPoly(f.pts, COLORS.grass, COLORS.grassLine, lw);
          } else if (f.key === 'bottom') {
            // the bed of the water, seen through the water box
            drawPoly(f.pts, COLORS.waterFloor, COLORS.waterLine, lw);
          } else {
            var light = 0.92 + 0.1 * (f.n[0] - f.n[1]);
            drawPoly(f.pts, shade(COLORS.dirt, light), COLORS.dirtLine, lw);
          }
        });
    }

    function drawWater() {
      if (waterVis < 0.02) return;
      ctx.globalAlpha = alpha * waterVis;
      waterFaces
        .map(function (f) { f.d = faceDepth(f.pts); return f; })
        .sort(function (a, b) { return (a.facing > 0) - (b.facing > 0) || a.d - b.d; })
        .forEach(function (f) {
          var up = f.n[2] > 0.5;
          var fill = 'rgba(' + COLORS.water + ',' + (up ? 0.62 : f.facing > 0 ? 0.55 : 0.35) + ')';
          drawPoly(f.pts, fill, COLORS.waterLine, lw);
        });
    }

    // Draw whichever block is further away first.
    var dirtCenter = place([0, 0, DIRT / 2], cos, sin, c[0], c[1], cz);
    var waterCenter = place([0, 0, -wh / 2], cos, sin, c[0], c[1], cz);
    if (depth(waterCenter[0], waterCenter[1], waterCenter[2]) < depth(dirtCenter[0], dirtCenter[1], dirtCenter[2])) {
      drawWater(); drawDirt();
    } else {
      drawDirt(); drawWater();
    }

    // Hint marker / keyboard cursor: an outline floating over the top of the tile.
    var topZ = cz + (tl.water ? wh : DIRT);
    if (game.hint === tl.k && tl.rot.done()) {
      var pulse = 0.5 + 0.5 * Math.sin((now - (game.hintAt || 0)) * 6);
      ctx.globalAlpha = alpha * (0.55 + 0.45 * pulse);
      outline(c, topZ + 2 + pulse * 6, '#ffffff', lw * 3.2);
      outline(c, topZ + 2 + pulse * 6, '#ff7a00', lw * 1.6);
    }
    if (game.cursorVisible && game.hover === tl.k && game.state === 'play') {
      ctx.globalAlpha = alpha * 0.9;
      outline(c, topZ + 1, '#3b2c0e', lw * 1.8, true);
    }
    ctx.globalAlpha = 1;
  }

  function outline(c, z, color, width, dashed) {
    var inset = H - 4;
    var pts = [[c[0] - inset, c[1] - inset, z], [c[0] + inset, c[1] - inset, z], [c[0] + inset, c[1] + inset, z], [c[0] - inset, c[1] + inset, z]];
    ctx.beginPath();
    pts.forEach(function (p, i) {
      var s = project(p[0], p[1], p[2]);
      if (i) ctx.lineTo(s[0], s[1]); else ctx.moveTo(s[0], s[1]);
    });
    ctx.closePath();
    ctx.setLineDash(dashed ? [6 * view.scale, 4 * view.scale] : []);
    ctx.strokeStyle = color;
    ctx.lineWidth = width;
    ctx.lineJoin = 'round';
    ctx.stroke();
    ctx.setLineDash([]);
  }

  function drawShadow() {
    // Soft shadow of the whole polder on the sand.
    ctx.save();
    ctx.beginPath();
    tiles.forEach(function (tl) {
      if (!tl.present) return;
      var a = tl.alpha.value();
      if (a < 0.5) return;
      var c = tileCenter(tl), s = H + 3, z = -14;
      var pts = [[c[0] - s, c[1] - s], [c[0] + s, c[1] - s], [c[0] + s, c[1] + s], [c[0] - s, c[1] + s]];
      pts.forEach(function (p, i) {
        var q = project(p[0], p[1], z);
        if (i) ctx.lineTo(q[0], q[1]); else ctx.moveTo(q[0], q[1]);
      });
      ctx.closePath();
    });
    ctx.fillStyle = 'rgba(150, 105, 35, 0.13)';
    ctx.fill('nonzero');
    ctx.restore();
  }

  function render() {
    ctx.setTransform(view.dpr, 0, 0, view.dpr, 0, 0);
    // Sand background with a soft light in the middle
    var g = ctx.createRadialGradient(view.w / 2, view.h * 0.48, 0, view.w / 2, view.h * 0.48, Math.max(view.w, view.h) * 0.7);
    g.addColorStop(0, '#fcecc2');
    g.addColorStop(1, '#f3daa0');
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, view.w, view.h);

    ctx.lineJoin = 'round';
    drawShadow();
    tiles
      .slice()
      .sort(function (a, b) { return tileDepth(a) - tileDepth(b) || a.col - b.col; })
      .forEach(drawTile);
  }

  // ------------------------------------------------------------------
  // Layout: fit the current polder into the free space between the HUD bars
  // ------------------------------------------------------------------
  var hudTop = document.querySelector('.hud-top');
  var hudBottom = document.querySelector('.hud-bottom');

  function boardBounds() {
    var minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity, any = false;
    tiles.forEach(function (tl) {
      if (!tl.present) return;
      any = true;
      var c = tileCenter(tl);
      [[-H, -H], [H, -H], [H, H], [-H, H]].forEach(function (o) {
        var x = c[0] + o[0], y = c[1] + o[1];
        var sx = x * cam.cosY - y * cam.sinY, d = x * cam.sinY + y * cam.cosY;
        [-(DIRT + 14), WATER + LIFT + 4].forEach(function (z) {
          var sy = d * cam.sinE - z * cam.cosE;
          minX = Math.min(minX, sx); maxX = Math.max(maxX, sx);
          minY = Math.min(minY, sy); maxY = Math.max(maxY, sy);
        });
      });
    });
    if (!any) return { minX: -200, maxX: 200, minY: -100, maxY: 100 };
    return { minX: minX, maxX: maxX, minY: minY, maxY: maxY };
  }

  function fitBoard() {
    var w = view.w, h = view.h;
    // Only narrow portrait screens (phones) need the front-facing view; tablets keep the original one.
    if (h > w * 1.2 && w < 600) setCamera(PORTRAIT_YAW, PORTRAIT_ELEV); else setCamera(45, 25);
    var topH = hudTop.offsetHeight, botH = hudBottom.offsetHeight;
    var landscape = w > h * 1.25;
    // In landscape the HUD sits in the corners, so the pointed top of the board may use the middle.
    var top = landscape ? Math.max(8, topH * 0.35) : topH + 8;
    var bottom = h - botH - (h < 460 ? 30 : 40);
    var side = w < 600 ? 10 : 24;
    var b = boardBounds();
    var bw = b.maxX - b.minX, bh = b.maxY - b.minY;
    var availW = w - side * 2, availH = Math.max(80, bottom - top);
    var s = Math.min(availW / bw, availH / bh, 3.4);
    view.scale = Math.max(0.3, s);
    view.ox = w / 2 - ((b.minX + b.maxX) / 2) * view.scale;
    view.oy = top + availH / 2 - ((b.minY + b.maxY) / 2) * view.scale;
  }

  function resize() {
    view.w = window.innerWidth;
    view.h = window.innerHeight;
    view.dpr = Math.min(window.devicePixelRatio || 1, 3);
    canvas.width = Math.round(view.w * view.dpr);
    canvas.height = Math.round(view.h * view.dpr);
    fitBoard();
  }

  // ------------------------------------------------------------------
  // Hit testing: silhouette of each tile, front tiles first
  // ------------------------------------------------------------------
  function hull(points) {
    points.sort(function (a, b) { return a[0] - b[0] || a[1] - b[1]; });
    var cross = function (o, a, b) { return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]); };
    var lower = [], upper = [], i;
    for (i = 0; i < points.length; i++) {
      while (lower.length >= 2 && cross(lower[lower.length - 2], lower[lower.length - 1], points[i]) <= 0) lower.pop();
      lower.push(points[i]);
    }
    for (i = points.length - 1; i >= 0; i--) {
      while (upper.length >= 2 && cross(upper[upper.length - 2], upper[upper.length - 1], points[i]) <= 0) upper.pop();
      upper.push(points[i]);
    }
    upper.pop(); lower.pop();
    return lower.concat(upper);
  }

  function inside(poly, x, y) {
    var ok = true;
    for (var i = 0; i < poly.length; i++) {
      var a = poly[i], b = poly[(i + 1) % poly.length];
      if ((b[0] - a[0]) * (y - a[1]) - (b[1] - a[1]) * (x - a[0]) < 0) { ok = false; break; }
    }
    return ok;
  }

  function tileAt(x, y) {
    var order = tiles.filter(function (tl) { return tl.present; })
      .sort(function (a, b) { return tileDepth(b) - tileDepth(a); });
    for (var i = 0; i < order.length; i++) {
      var tl = order[i], c = tileCenter(tl);
      var top = tl.water ? WATER : DIRT;   // static: hovering must not move the hit areas
      var pts = [];
      [[-H, -H], [H, -H], [H, H], [-H, H]].forEach(function (o) {
        pts.push(project(c[0] + o[0], c[1] + o[1], -2));
        pts.push(project(c[0] + o[0], c[1] + o[1], top));
      });
      if (inside(hull(pts), x, y)) return tl.k;
    }
    return -1;
  }

  // ------------------------------------------------------------------
  // Input: pointer events (mouse, touch, pen) and keyboard
  // ------------------------------------------------------------------
  function localPoint(e) {
    var r = canvas.getBoundingClientRect();
    return [e.clientX - r.left, e.clientY - r.top];
  }

  function setHover(k, withSound) {
    if (k === game.hover) return;
    game.hover = k;
    if (k >= 0 && withSound && game.state === 'play' && now >= game.readyAt) audio.play('hover', 0.5);
    canvas.classList.toggle('pointer', k >= 0 && game.state === 'play');
    updateLift();
  }

  canvas.addEventListener('pointerdown', function (e) {
    audio.unlock();
    if (game.state !== 'play') return;
    e.preventDefault();
    game.cursorVisible = false;
    var p = localPoint(e);
    var k = tileAt(p[0], p[1]);
    game.pressed = k;
    game.pointerType = e.pointerType;
    try { canvas.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    setHover(k, e.pointerType !== 'mouse');
  });

  canvas.addEventListener('pointermove', function (e) {
    if (game.state !== 'play') return;
    var p = localPoint(e);
    if (e.pointerType === 'mouse') {
      game.cursorVisible = false;
      setHover(tileAt(p[0], p[1]), true);
    } else if (game.pressed >= 0) {
      // finger slid away: preview follows, press happens on release
      var k = tileAt(p[0], p[1]);
      game.pressed = k;
      setHover(k, true);
    }
  });

  canvas.addEventListener('pointerup', function (e) {
    if (game.state !== 'play') return;
    var p = localPoint(e);
    var k = tileAt(p[0], p[1]);
    if (k >= 0 && k === game.pressed) press(k);
    game.pressed = -1;
    if (e.pointerType !== 'mouse') setHover(-1);
    else setHover(tileAt(p[0], p[1]));
  });

  canvas.addEventListener('pointercancel', function () { game.pressed = -1; setHover(-1); });
  canvas.addEventListener('pointerleave', function (e) { if (e.pointerType === 'mouse') setHover(-1); });
  canvas.addEventListener('contextmenu', function (e) { e.preventDefault(); });
  document.addEventListener('contextmenu', function (e) { e.preventDefault(); });

  function firstPresent() {
    for (var i = 0; i < CELLS; i++) if (tiles[i].present) return i;
    return -1;
  }

  window.addEventListener('keydown', function (e) {
    audio.unlock();
    if (game.state === 'menu') {
      if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); startGame(false); }
      return;
    }
    if (game.state !== 'play') return;
    var dirs = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1],
      a: [-1, 0], d: [1, 0], w: [0, -1], s: [0, 1] };
    var key = e.key.length === 1 ? e.key.toLowerCase() : e.key;
    if (dirs[key]) {
      e.preventDefault();
      var cur = game.hover >= 0 ? game.hover : firstPresent();
      if (game.cursorVisible && game.hover >= 0) {
        // move to the next present tile in that direction
        var x = cur % N, y = (cur / N) | 0;
        for (var step = 1; step < N; step++) {
          var nx = x + dirs[key][0] * step, ny = y + dirs[key][1] * step;
          if (nx < 0 || ny < 0 || nx >= N || ny >= N) break;
          if (tiles[ny * N + nx].present) { cur = ny * N + nx; break; }
        }
      }
      game.cursorVisible = true;
      game.hover = -2; // force refresh
      setHover(cur, true);
    } else if (key === 'Enter' || key === ' ') {
      if (e.target && e.target.closest && e.target.closest('button')) return; // let the focused button handle it
      e.preventDefault();
      if (game.cursorVisible && game.hover >= 0) press(game.hover);
    } else if (key === 'r') {
      resetLevel();
    } else if (key === 'h') {
      showHint();
    } else if (key === 'm') {
      toggleMute();
    }
  });

  // ------------------------------------------------------------------
  // HUD, buttons and menu
  // ------------------------------------------------------------------
  var levelLabel = document.getElementById('levelLabel');
  var movesLabel = document.getElementById('movesLabel');
  var parLabel = document.getElementById('parLabel');
  var message = document.getElementById('message');
  var banner = document.getElementById('banner');
  var bannerTitle = document.getElementById('bannerTitle');
  var bannerSub = document.getElementById('bannerSub');
  var bannerPerfect = document.getElementById('bannerPerfect');
  var resetBtn = document.getElementById('resetBtn');
  var hintBtn = document.getElementById('hintBtn');
  var muteBtn = document.getElementById('muteBtn');
  var menu = document.getElementById('menu');
  var playBtn = document.getElementById('playBtn');
  var newGameBtn = document.getElementById('newGameBtn');
  var ruleText = document.getElementById('ruleText');
  var messageTimer = 0;

  var coarse = window.matchMedia && window.matchMedia('(pointer: coarse)').matches;
  ruleText.textContent = (coarse ? 'Tap' : 'Click') + ' a tile to flip it together with its four neighbours: ' +
    'water turns into land and land turns back into water. Drain every tile to clear the level.';

  function updateHud() {
    levelLabel.textContent = 'Level ' + game.level;
    movesLabel.textContent = game.moves;
    parLabel.textContent = game.par;
  }

  function showMessage(text, seconds) {
    message.textContent = text;
    message.classList.add('show');
    messageTimer = now + (seconds || 3);
  }
  function hideMessage() { message.classList.remove('show'); messageTimer = 0; }

  function toggleMute() {
    audio.muted = !audio.muted;
    store.set('muted', audio.muted);
    muteBtn.setAttribute('aria-pressed', audio.muted ? 'true' : 'false');
    muteBtn.setAttribute('aria-label', audio.muted ? 'Unmute sound' : 'Mute sound');
    if (!audio.muted) { audio.unlock(); }
  }

  function startGame(fresh) {
    audio.unlock();
    menu.classList.add('hidden');
    game.state = 'play';
    if (fresh) loadLevel(1);
    else game.readyAt = Math.max(game.readyAt, now + 0.1);
    if (game.level === 1) {
      showMessage((coarse ? 'Tap' : 'Click') + ' a tile to flip it and its neighbours', 5);
    }
    updateHud();
  }

  resetBtn.addEventListener('click', function () { audio.unlock(); resetLevel(); });
  hintBtn.addEventListener('click', function () { audio.unlock(); showHint(); });
  muteBtn.addEventListener('click', toggleMute);
  playBtn.addEventListener('click', function () { startGame(false); });
  newGameBtn.addEventListener('click', function () { startGame(true); });
  // Keep button taps from reaching the canvas / page
  [resetBtn, hintBtn, muteBtn].forEach(function (b) {
    b.addEventListener('pointerdown', function (e) { e.stopPropagation(); audio.unlock(); });
  });

  muteBtn.setAttribute('aria-pressed', audio.muted ? 'true' : 'false');
  if (game.level > 1) {
    playBtn.textContent = 'Continue · Level ' + game.level;
    newGameBtn.hidden = false;
  } else {
    newGameBtn.hidden = true;
  }

  // ------------------------------------------------------------------
  // Main loop (requestAnimationFrame stops while the tab is hidden,
  // and the clock never jumps, so nothing breaks in the background)
  // ------------------------------------------------------------------
  var lastFrame = 0;
  function frame(ts) {
    var dt = lastFrame ? (ts - lastFrame) / 1000 : 0;
    lastFrame = ts;
    now += Math.min(dt, 0.1);

    // run scheduled events
    if (game.events.length) {
      var due = game.events.filter(function (ev) { return ev[0] <= now; });
      if (due.length) {
        game.events = game.events.filter(function (ev) { return ev[0] > now; });
        due.forEach(function (ev) { ev[1](); });
      }
    }
    if (messageTimer && now > messageTimer) hideMessage();

    hintBtn.disabled = game.state !== 'play';
    resetBtn.disabled = game.state !== 'play';

    render();
    requestAnimationFrame(frame);
  }

  document.addEventListener('visibilitychange', function () {
    lastFrame = 0;
    if (!audio.ctx) return;
    if (document.hidden) audio.ctx.suspend(); else audio.ctx.resume();
  });

  window.addEventListener('resize', resize);
  window.addEventListener('orientationchange', function () { setTimeout(resize, 150); });
  if (window.visualViewport) window.visualViewport.addEventListener('resize', resize);

  resize();
  loadLevel(game.level);
  requestAnimationFrame(frame);

  // Small read-only hook used by automated tests / screenshot scripts.
  window.dryLand = {
    get state() { return game.state; },
    get level() { return game.level; },
    get moves() { return game.moves; },
    get hover() { return game.hover; },
    solution: function () { return solve(presentMask(), waterMask()); },
    tileScreenPos: function (k) {
      var tl = tiles[k], c = tileCenter(tl);
      return project(c[0], c[1], tl.water ? WATER : DIRT);
    }
  };
})();
