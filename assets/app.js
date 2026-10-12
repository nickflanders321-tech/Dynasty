// Retirement Dynasty site. Reads data/league.json (written every 10 minutes by
// fetch-sleeper.mjs on GitHub Actions) and renders every page client-side.
// Pages are hash routes (#/team/<id>, #/h2h/<a>/<b>, ...) so any view can be
// shared as a link.
(function () {
'use strict';

/* =====================================================================
   Small helpers
   ===================================================================== */
const $ = (s, el = document) => el.querySelector(s);
const $$ = (s, el = document) => [...el.querySelectorAll(s)];
const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const f = (n, d = 1) => Number(n || 0).toLocaleString('en-US', { minimumFractionDigits: d, maximumFractionDigits: d });
const f2 = n => f(n, 2), f0 = n => f(n, 0);
const sg = (n, d = 1) => (n > 0 ? '+' : n < 0 ? '−' : '') + f(Math.abs(n), d);
const cls = n => n > 0 ? 'win' : n < 0 ? 'loss' : '';
const mean = a => a.length ? a.reduce((x, y) => x + y, 0) / a.length : 0;
const sd = a => { const m = mean(a); return Math.sqrt(mean(a.map(x => (x - m) ** 2))) || 0; };
const sdz = a => sd(a) || 1;
const median = a => { const v = a.slice().sort((x, y) => x - y), n = v.length; return !n ? 0 : n % 2 ? v[(n - 1) / 2] : (v[n / 2 - 1] + v[n / 2]) / 2; };
const ord = n => { const s = ['th', 'st', 'nd', 'rd'], v = n % 100; return n + (s[(v - 20) % 10] || s[v] || s[0]); };
const plural = (n, w, p) => `${n} ${n === 1 ? w : (p || w + 's')}`;
const r2 = x => Math.round(x * 100) / 100;
const pick = a => a[Math.floor(Math.random() * a.length)];
const LS = {
  get(k) { try { return localStorage.getItem(k); } catch (e) { return null; } },
  set(k, v) { try { v == null ? localStorage.removeItem(k) : localStorage.setItem(k, v); } catch (e) { /* storage off */ } }
};
const K = 2.37; // Pythagorean exponent for expected wins
const tdate = ts => new Date(ts).toLocaleDateString('en-US', { month: 'short', day: 'numeric', year: 'numeric' });
const ago = ts => { const m = Math.round((Date.now() - new Date(ts)) / 60000); return m < 1 ? 'just now' : m < 60 ? `${m} min ago` : m < 60 * 24 ? `${Math.round(m / 60)} hr ago` : tdate(ts); };
// All entries tied for the best value, so ties are never decided by array order.
function tops(list, fn, dir = 1) {
  const ok = list.filter(x => Number.isFinite(fn(x)));
  if (!ok.length) return { v: null, items: [] };
  const best = dir > 0 ? Math.max(...ok.map(x => r2(fn(x)))) : Math.min(...ok.map(x => r2(fn(x))));
  const items = ok.filter(x => r2(fn(x)) === best);
  return { v: fn(items[0]), items };
}
const andList = a => a.length <= 1 ? (a[0] || '') : a.length === 2 ? `${a[0]} & ${a[1]}` : `${a.slice(0, -1).join(', ')} & ${a[a.length - 1]}`;

/* =====================================================================
   State
   ===================================================================== */
let D = null;   // raw league.json
let M = null;   // computed model
let ME = LS.get('rd-me');
const segMemory = {}; // pill positions before a re-render, so selectors glide

/* =====================================================================
   Data model
   ===================================================================== */
function buildModel(D) {
  const S = D.seasons.slice().sort((a, b) => Number(a.season) - Number(b.season));
  const cur = S[S.length - 1], ST = D.state || {};
  const inSeason = (ST.season_type === 'regular' || ST.season_type === 'post') && String(ST.season) === String(cur.season);
  const nowW = inSeason ? Number(ST.week) : 99;
  const ps = s => s.settings.playoff_week_start || 15;
  const hasMed = s => !!s.settings.median;
  const regW = s => ps(s) - 1;
  const wkTot = w => w.games.reduce((n, g) => n + g[1] + g[3], 0);
  const isFinal = (s, w) => s !== cur || !inSeason || w < nowW;
  const NAMES = D.names || {}, POS = D.pos || {};

  // ---- managers (keyed by Sleeper user id, so they carry across seasons) ----
  const TM = {};
  S.forEach(s => {
    s.map = {}; s.rmap = {};
    s.teams.forEach(t => {
      const k = t.owner_id || `${s.season}-${t.roster_id}`;
      s.map[t.roster_id] = k; s.rmap[k] = t.roster_id;
      const o = TM[k] || (TM[k] = { key: k, seasons: [] });
      o.name = t.team_name || t.display_name || o.name || ('Team ' + t.roster_id);
      o.user = t.display_name || o.user || '';
      if (t.avatar) o.avatar = t.avatar;
      o.seasons.push(s.season);
    });
  });
  const hue = k => { let h = 0; for (const c of String(k)) h = (h * 31 + c.charCodeAt(0)) >>> 0; return h % 360; };
  Object.values(TM).forEach(t => {
    t.hue = hue(t.key);
    const w = t.name.replace(/[^A-Za-z0-9 ]/g, ' ').split(/\s+/).filter(Boolean);
    t.ini = ((w.length > 1 ? w[0][0] + w[1][0] : (w[0] || '?').slice(0, 2)) || '?').toUpperCase();
    t.current = t.seasons.includes(cur.season);
  });
  const TEAMS = cur.teams.slice().sort((a, b) => a.roster_id - b.roster_id).map(t => TM[cur.map[t.roster_id]]);
  // Short codes for dense matrices.
  const used = new Set();
  Object.values(TM).forEach(t => {
    const c = (t.name.split(/\s+/).map(w => w[0] || '').join('').replace(/[^A-Za-z0-9]/g, '').slice(0, 3).toUpperCase()) || 'T';
    let u = c, i = 2; while (used.has(u)) u = c.slice(0, 2) + (i++); used.add(u); t.code = u;
  });

  // ---- season standings ----
  const SS = {};
  S.forEach(s => {
    const m = hasMed(s), tot = regW(s) * (m ? 2 : 1);
    const rows = s.standings.map(r => {
      const key = s.map[r.roster_id], n = r.w + r.l + (r.t || 0), wk = m ? n / 2 : n;
      const py = (r.pf > 0 && r.pa > 0) ? Math.pow(r.pf, K) / (Math.pow(r.pf, K) + Math.pow(r.pa, K)) : .5;
      return { key, rid: r.roster_id, w: r.w, l: r.l, t: r.t || 0, pf: r.pf, pa: r.pa, pp: r.pp, rec: r.record || '', n, wk,
        ppg: wk ? r.pf / wk : 0, pag: wk ? r.pa / wk : 0, eff: r.pp ? r.pf / r.pp * 100 : 0, diff: r.pf - r.pa,
        pyth: py, xw: py * n, luck: r.w - py * n, wp: n ? r.w / n : 0, proj: (n ? r.w / n : 0) * tot };
    }).sort((a, b) => b.w - a.w || b.pf - a.pf);
    rows.forEach((r, i) => r.rank = i + 1);
    SS[s.season] = rows;
  });
  const CS = SS[cur.season];
  const CSM = {}; CS.forEach(r => CSM[r.key] = r);

  // ---- playoff brackets ----
  S.forEach(s => {
    const B = s.bracket || [];
    s.maxR = Math.max(0, ...B.map(m => m.r));
    s.inPO = new Set(); B.forEach(m => { if (m.t1 != null) s.inPO.add(s.map[m.t1]); if (m.t2 != null) s.inPO.add(s.map[m.t2]); });
    s.place = {};
    B.forEach(m => { if (m.p && m.w != null && m.l != null) { s.place[s.map[m.w]] = m.p; s.place[s.map[m.l]] = m.p + 1; } });
    const c = B.find(m => m.p === 1 && m.w != null);
    s.champ = c ? s.map[c.w] : null; s.runner = c ? s.map[c.l] : null;
    const t3 = B.find(m => m.p === 3 && m.w != null); s.third = t3 ? s.map[t3.w] : null;
  });
  const roundName = (s, m) => m.p === 1 ? 'Championship' : m.p === 3 ? '3rd place game' : m.p ? ord(m.p) + ' place game' : m.r === s.maxR - 1 ? 'Semifinal' : m.r === s.maxR - 2 ? 'Quarterfinal' : 'Playoffs round ' + m.r;
  const done = S.filter(s => s !== cur || !inSeason);
  const finished = S.filter(s => s.champ);

  // ---- every game, plus each week's scores, median and lineups ----
  const G = [];
  const WK = {}; // season -> week -> {...}
  S.forEach(s => {
    WK[s.season] = {};
    s.weeks.forEach(wk => {
      const games = wk.games.map(g => ({ ra: g[0], sa: g[1], rb: g[2], sb: g[3], a: s.map[g[0]], b: s.map[g[2]] })).filter(g => g.a && g.b);
      const sc = {}; games.forEach(g => { sc[g.a] = g.sa; sc[g.b] = g.sb; });
      const vals = Object.values(sc);
      const lu = {}; Object.entries(wk.lu || {}).forEach(([rid, l]) => { if (s.map[rid]) lu[s.map[rid]] = l; });
      const reg = wk.week < ps(s);
      const final = isFinal(s, wk.week), tot = wkTot(wk);
      const W = WK[s.season][wk.week] = { s, w: wk.week, games, sc, md: median(vals), mx: Math.max(...vals), mn: Math.min(...vals), lu, reg, final, scored: tot > 0, gids: [] };
      const sorted = Object.keys(sc).sort((x, y) => sc[y] - sc[x]);
      W.rank = {}; sorted.forEach((k, i) => W.rank[k] = i + 1);
      if (!final || tot <= 0) return;
      games.forEach(g => {
        let type = 'reg', label = 'Week ' + wk.week;
        if (!reg) {
          const r = wk.week - ps(s) + 1;
          const m = (s.bracket || []).find(x => x.r === r && ((x.t1 === g.ra && x.t2 === g.rb) || (x.t1 === g.rb && x.t2 === g.ra)));
          if (m) { type = m.p === 1 ? 'final' : 'po'; label = roundName(s, m); }
          else if ((s.bracket || []).length) { type = 'cons'; label = 'Consolation'; }
          else { type = 'po'; label = 'Playoffs'; }
        }
        const win = g.sa >= g.sb ? g.a : g.b, lose = g.sa >= g.sb ? g.b : g.a;
        const o = { id: G.length, s, y: s.season, w: wk.week, a: g.a, b: g.b, sa: g.sa, sb: g.sb, type, label,
          win, lose, ws: Math.max(g.sa, g.sb), ls: Math.min(g.sa, g.sb), m: Math.abs(g.sa - g.sb), tot: g.sa + g.sb, tie: g.sa === g.sb, W };
        W.gids.push(o.id);
        G.push(o);
      });
    });
  });
  const GH = G.filter(g => g.type !== 'cons'); // head-to-head games that count (regular season + real playoff games)
  const gameLabel = g => `${g.y} · ${g.label}`;

  // ---- per-season weekly breakdown (regular season, finished weeks) ----
  const WCache = {};
  function weekly(s) {
    if (WCache[s.season]) return WCache[s.season];
    const wks = Object.values(WK[s.season]).filter(w => w.reg && w.final && w.scored).sort((a, b) => a.w - b.w);
    const T = {};
    wks.forEach(wk => {
      const n = Object.keys(wk.sc).length;
      Object.keys(wk.sc).forEach(k => {
        const t = T[k] || (T[k] = { k, sc: [], wks: [], hw: 0, hl: 0, mw: 0, ml: 0, ap: 0, apn: 0, lw: 0, ul: 0, cr: 0, lo: 0, ranks: [] });
        const x = wk.sc[k], g = wk.games.find(q => q.a === k || q.b === k), os = g.a === k ? g.sb : g.sa;
        t.sc.push(x); t.wks.push(wk.w); t.ranks.push(wk.rank[k]);
        const won = x > os; won ? t.hw++ : t.hl++;
        const ab = x > wk.md; ab ? t.mw++ : t.ml++;
        if (won && !ab) t.lw++; if (!won && ab) t.ul++;
        t.ap += Object.keys(wk.sc).filter(o => o !== k && wk.sc[o] < x).length; t.apn += n - 1;
        if (x === wk.mx) t.cr++; if (x === wk.mn) t.lo++;
      });
    });
    Object.values(T).forEach(t => { t.sd = sd(t.sc); t.avg = mean(t.sc); t.hi = Math.max(...t.sc); t.low = Math.min(...t.sc); });
    return (WCache[s.season] = { wks, T });
  }

  // ---- streak strings across seasons (each season's game-by-game W/L, median games included) ----
  const runs = (str, c) => Math.max(0, ...(str || '').split(c === 'W' ? 'L' : 'W').map(x => x.replace(/T/g, '').length));
  const curRun = str => { if (!str) return null; const c = str.slice(-1); let n = 0; for (let i = str.length - 1; i >= 0 && str[i] === c; i--) n++; return { c, n }; };
  const REC = {};
  Object.values(TM).forEach(t => { REC[t.key] = S.map(s => { const r = SS[s.season].find(x => x.key === t.key); return r ? r.rec : ''; }).join(''); });

  // ---- head-to-head matrix ----
  const HH = {};
  const hh = (a, b) => ((HH[a] || (HH[a] = {}))[b] || (HH[a][b] = { w: 0, l: 0, t: 0, pf: 0, pa: 0, g: [] }));
  GH.forEach(g => {
    const A = hh(g.a, g.b), B = hh(g.b, g.a);
    A.pf += g.sa; A.pa += g.sb; B.pf += g.sb; B.pa += g.sa; A.g.push(g); B.g.push(g);
    if (g.tie) { A.t++; B.t++; } else if (g.win === g.a) { A.w++; B.l++; } else { A.l++; B.w++; }
  });

  // ---- power rankings (current season) ----
  const zs = (a, k) => { const m = mean(a.map(x => x[k])), d = sdz(a.map(x => x[k])); a.forEach(x => x['z' + k] = (x[k] - m) / d); };
  ['ppg', 'wp', 'eff', 'pyth'].forEach(k => zs(CS, k));
  CS.forEach(t => t.pow = t.zppg * .4 + t.zwp * .25 + t.zeff * .15 + t.zpyth * .2);
  const PW = CS.slice().sort((a, b) => b.pow - a.pow);

  // ---- careers ----
  const CAR = {};
  Object.values(TM).forEach(t => {
    const seasons = S.filter(s => s.rmap[t.key] != null).map(s => {
      const r = SS[s.season].find(x => x.key === t.key);
      return { s, y: s.season, r, rank: r ? r.rank : null, po: s.inPO.has(t.key), place: s.place[t.key] || null, champ: s.champ === t.key, runner: s.runner === t.key, live: s === cur && inSeason };
    });
    const gs = GH.filter(g => g.a === t.key || g.b === t.key);
    const res = gs.map(g => ({ g, me: g.a === t.key ? g.sa : g.sb, opp: g.a === t.key ? g.b : g.a, os: g.a === t.key ? g.sb : g.sa }));
    let w = 0, l = 0, pf = 0, pa = 0, n = 0;
    seasons.forEach(x => { if (x.r) { w += x.r.w; l += x.r.l; pf += x.r.pf; pa += x.r.pa; n += x.r.wk; } });
    const reg = res.filter(x => x.g.type === 'reg'), po = res.filter(x => x.g.type !== 'reg');
    let ap = 0, apn = 0, hiW = 0, loW = 0; const ranks = [];
    S.forEach(s => { const T = weekly(s).T[t.key]; if (T) { ap += T.ap; apn += T.apn; hiW += T.cr; loW += T.lo; ranks.push(...T.ranks); } });
    CAR[t.key] = {
      t, seasons, res, w, l, pf, pa, n, ppg: n ? pf / n : 0, wp: (w + l) ? w / (w + l) : 0,
      hw: res.filter(x => x.me > x.os).length, hl: res.filter(x => x.me < x.os).length,
      regW: reg.filter(x => x.me > x.os).length, regL: reg.filter(x => x.me < x.os).length,
      poW: po.filter(x => x.me > x.os).length, poL: po.filter(x => x.me < x.os).length,
      titles: seasons.filter(x => x.champ).map(x => x.y), runners: seasons.filter(x => x.runner).map(x => x.y),
      apps: seasons.filter(x => x.po && !x.live).length, ap, apn, hiW, loW, ranks,
      ws: runs(REC[t.key], 'W'), ls: runs(REC[t.key], 'L'), cur: curRun(REC[t.key]),
      avgRank: mean(seasons.filter(x => x.rank && !x.live).map(x => x.rank))
    };
  });

  // ---- player performances from saved lineups ----
  const PG = []; // {pid, pts, k, g}
  G.forEach(g => {
    if (g.type === 'cons') return;
    [g.a, g.b].forEach(k => (g.W.lu[k] || []).forEach(([pid, pts]) => PG.push({ pid, pts, k, g })));
  });
  const hasLineups = PG.length > 0;
  const pname = pid => NAMES[pid] || (/^[A-Z]{2,3}$/.test(pid) ? pid + ' Defense' : 'Player #' + pid);
  const ppos = pid => POS[pid] || (/^[A-Z]{2,3}$/.test(pid) ? 'DEF' : '');

  // ---- trades ----
  const TRD = [];
  S.forEach(s => (s.trades || []).forEach(t => { const keys = (t.rosters || []).map(r => s.map[r]).filter(Boolean); if (keys.length >= 2) TRD.push({ ...t, s, keys }); }));
  TRD.sort((a, b) => b.ts - a.ts);
  const allDrafts = S.flatMap(s => (s.drafts || []).map(d => ({ ...d, s })));

  const scoredWeeks = Object.values(WK[cur.season]).filter(w => w.scored && (!inSeason || w.w <= nowW)).map(w => w.w).sort((a, b) => a - b);
  const liveWeek = inSeason && scoredWeeks.includes(nowW) && !isFinal(cur, nowW) ? nowW : null;
  const lastFinal = Math.max(0, ...Object.values(WK[cur.season]).filter(w => w.final && w.scored && w.reg).map(w => w.w));
  const nextWk = inSeason ? Object.values(WK[cur.season]).filter(w => !w.scored && w.w > Math.max(0, ...scoredWeeks)).sort((a, b) => a.w - b.w)[0] || null : null;

  return { S, cur, ST, inSeason, nowW, ps, hasMed, regW, isFinal, TM, TEAMS, SS, CS, CSM, G, GH, WK, weekly, REC, runs, curRun, HH, hh, PW, CAR, PG, hasLineups, pname, ppos,
    TRD, allDrafts, done, finished, scoredWeeks, liveWeek, lastFinal, nextWk, gameLabel, leagueName: cur.name || 'Fantasy League', cutN: (cur.settings.playoff_teams || 6) };
}

/* =====================================================================
   Shared renderers
   ===================================================================== */
const T = k => M.TM[k] || { key: k, name: 'Unknown', user: '', hue: 0, ini: '?' };
const nm = k => esc(T(k).name);
function av(k, size = '') {
  const t = T(k);
  return `<span class="av ${size}" style="--h:${t.hue}" aria-hidden="true">${esc(t.ini)}${t.avatar ? `<img src="${esc(t.avatar)}" alt="" loading="lazy" onerror="this.remove()">` : ''}</span>`;
}
function tm(k, { sub = true, size = '', link = true, extra = '' } = {}) {
  const t = T(k);
  const inner = `${av(k, size)}<span class="tm-t"><span class="tm-n">${esc(t.name)}${extra}</span>${sub && t.user && t.user !== t.name ? `<span class="tm-u">${esc(t.user)}</span>` : ''}</span>`;
  return link ? `<a class="tm" href="#/team/${encodeURIComponent(k)}">${inner}</a>` : `<span class="tm">${inner}</span>`;
}
const meCls = k => k === ME ? ' me-row' : '';
const card = (title, body, { note = '', right = '', cls = '', id = '' } = {}) => `<section class="glass card rise ${cls}"${id ? ` id="${id}"` : ''}>${title ? `<h2 class="card-title"><span>${title}</span>${right}</h2>` : ''}${note ? `<p class="note">${note}</p>` : ''}${body}</section>`;
const table = (head, rows, { cut = -1, stick = true, rowCls = () => '', left = 2 } = {}) =>
  `<div class="tbl"><table><thead><tr>${head.map((h, i) => `<th class="${i < left ? 'l' : ''}${i === 1 && stick ? ' stick' : ''}">${h}</th>`).join('')}</tr></thead><tbody>${rows.map((r, ri) => `<tr class="${ri === cut ? 'cut' : ''}${rowCls(ri)}">${r.map((c, i) => `<td class="${i < left ? 'l' : ''}${i === 1 && stick ? ' stick' : ''}">${c}</td>`).join('')}</tr>`).join('')}</tbody></table></div>`;
const dots = s => `<span class="dots">${(s || '').split('').map(c => `<i class="${c}"></i>`).join('')}</span>`;
const tiles = a => `<div class="tiles">${a.map(x => `<div class="tile${x[3] ? ' tap' : ''}"${x[3] ? ` onclick="${x[3]}"` : ''}><div class="t">${x[0]}</div><div class="n">${x[1]}</div><div class="v">${x[2]}</div></div>`).join('')}</div>`;
const posBadge = p => p ? `<span class="pos pos-${esc(p)}">${esc(p === 'DEF' ? 'DST' : p)}</span>` : '';
function seg(id, opts, active, onPick, { full = false, cls = '' } = {}) {
  // opts: [[value, label], ...]; onPick is a global function name taking the value.
  return `<div class="seg${full ? ' full' : ''} ${cls}" data-seg="${id}" role="tablist"><span class="pill-bg"></span>${opts.map(([v, l]) => `<button type="button" role="tab" aria-selected="${String(v) === String(active)}" class="${String(v) === String(active) ? 'on' : ''}" onclick="${onPick}('${esc(String(v))}')">${l}</button>`).join('')}</div>`;
}
function teamSelect(id, active, onchange, keys) {
  const list = keys || Object.keys(M.TM);
  const cur = list.filter(k => T(k).current), past = list.filter(k => !T(k).current);
  const o = k => `<option value="${esc(k)}"${k === active ? ' selected' : ''}>${esc(T(k).name)}</option>`;
  return `<select class="sel" id="${id}" onchange="${onchange}">${cur.map(o).join('')}${past.length ? `<optgroup label="Former managers">${past.map(o).join('')}</optgroup>` : ''}</select>`;
}
function pageHead(eyebrow, title, sub = '') {
  return `<header class="page-head rise"><div style="min-width:0"><div class="eyebrow">${eyebrow}</div><h1 class="h1">${title}</h1>${sub ? `<div class="sub">${sub}</div>` : ''}</div><button class="share" type="button" onclick="RD.share()" aria-label="Share this page"><svg class="share-ic" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3v13M7 8l5-5 5 5M5 14v5a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2v-5"/></svg>Share</button></header>`;
}

/* ---------- gliding selector pill ---------- */
function rememberSegs() { $$('.seg[data-seg]').forEach(s => { const p = $('.pill-bg', s); if (p && p.style.width) segMemory[s.dataset.seg] = { left: p.style.left, width: p.style.width, scroll: s.scrollLeft }; }); }
function placeSegs() {
  $$('.seg[data-seg]').forEach(s => {
    const on = $('button.on', s), p = $('.pill-bg', s);
    if (!on || !p) return;
    const prev = segMemory[s.dataset.seg]; delete segMemory[s.dataset.seg];
    if (prev) { s.scrollLeft = prev.scroll; p.style.transition = 'none'; p.style.left = prev.left; p.style.width = prev.width; void p.offsetWidth; p.style.transition = ''; }
    p.style.left = on.offsetLeft + 'px'; p.style.width = on.offsetWidth + 'px';
    // keep the chosen option in view on narrow screens
    const target = on.offsetLeft - (s.clientWidth - on.offsetWidth) / 2;
    if (on.offsetLeft < s.scrollLeft || on.offsetLeft + on.offsetWidth > s.scrollLeft + s.clientWidth) s.scrollTo({ left: Math.max(0, target), behavior: prev ? 'smooth' : 'auto' });
    fadeEdges(s);
    if (!s.dataset.fx) { s.dataset.fx = 1; s.addEventListener('scroll', () => fadeEdges(s), { passive: true }); }
  });
}
function fadeEdges(el) {
  const l = el.scrollLeft > 2, r = el.scrollLeft + el.clientWidth < el.scrollWidth - 2;
  el.classList.toggle('fade-l', l); el.classList.toggle('fade-r', r);
}

/* ---------- sheets ---------- */
function openSheet(title, sub, body) {
  closeSheet(true);
  const scrim = document.createElement('div'); scrim.className = 'scrim'; scrim.id = 'scrim';
  const sh = document.createElement('div'); sh.className = 'sheet'; sh.id = 'sheet'; sh.setAttribute('role', 'dialog'); sh.setAttribute('aria-modal', 'true'); sh.setAttribute('aria-label', title.replace(/<[^>]+>/g, ''));
  sh.innerHTML = `<div class="sheet-grab"><i></i></div><div class="sheet-head"><div style="min-width:0"><div class="t">${title}</div>${sub ? `<div class="s">${sub}</div>` : ''}</div><button class="x-btn" type="button" aria-label="Close" onclick="RD.closeSheet()">✕</button></div><div class="sheet-body">${body}</div>`;
  document.body.append(scrim, sh);
  scrim.onclick = () => closeSheet();
  document.documentElement.style.overflow = 'hidden';
  // swipe down to close on phones
  let y0 = null, dy = 0;
  const start = e => { y0 = e.touches[0].clientY; dy = 0; sh.style.transition = 'none'; };
  const move = e => { if (y0 == null) return; dy = Math.max(0, e.touches[0].clientY - y0); sh.style.transform = `translateY(${dy}px)`; };
  const end = () => { if (y0 == null) return; y0 = null; sh.style.transition = 'transform .2s'; if (dy > 90) closeSheet(); else sh.style.transform = ''; };
  [$('.sheet-grab', sh), $('.sheet-head', sh)].forEach(h => { h.addEventListener('touchstart', start, { passive: true }); h.addEventListener('touchmove', move, { passive: true }); h.addEventListener('touchend', end); });
  setTimeout(() => $('.x-btn', sh).focus({ preventScroll: true }), 50);
}
function closeSheet(instant) {
  const s = $('#sheet'), c = $('#scrim');
  if (s) s.remove(); if (c) c.remove();
  document.documentElement.style.overflow = '';
}
document.addEventListener('keydown', e => { if (e.key === 'Escape') { closeSheet(); closeNav(); } });

function toast(msg) { $$('.toast').forEach(x => x.remove()); const t = document.createElement('div'); t.className = 'toast'; t.textContent = msg; document.body.append(t); setTimeout(() => t.remove(), 2300); }

/* ---------- a game's two lineups ---------- */
function slotLabel(s, i) { const r = (s.settings.roster_positions || [])[i]; return r ? r.replace('SUPER_FLEX', 'SF').replace('REC_FLEX', 'WR/TE').replace('WRRB_FLEX', 'W/R') : ''; }
function lineupCol(g, k, score, won) {
  const l = g.W.lu[k] || [];
  const best = Math.max(0, ...l.map(x => x[1]));
  return `<div class="lu-col"><div class="lu-head"><div style="min-width:0">${tm(k, { sub: false, size: 'sm' })}</div><div class="sb ${won ? 'gold' : 'dim'}">${f2(score)}</div></div>${l.length ? l.map(([pid, pts], i) => `<div class="lu-p${pts === 0 ? ' zero' : ''}${pts === best && pts > 0 ? ' big' : ''}" title="${esc(slotLabel(g.s, i))}">${posBadge(M.ppos(pid))}<span class="nm">${esc(M.pname(pid))}</span><span class="pt">${f2(pts)}</span></div>`).join('') : `<div class="empty" style="padding:14px 4px">Lineups appear after the next data update.</div>`}</div>`;
}
function openGame(id) {
  const g = M.G[id]; if (!g) return;
  const aw = g.sa > g.sb, bw = g.sb > g.sa;
  openSheet(`${f2(g.ws)}–${f2(g.ls)}`, `${esc(g.y)} · ${esc(g.label)} · ${g.tie ? 'Tied' : `${nm(g.win)} by ${f2(g.m)}`}`,
    `<div class="lu">${lineupCol(g, g.a, g.sa, aw)}${lineupCol(g, g.b, g.sb, bw)}</div><div class="mt" style="text-align:center"><a class="link" href="#/h2h/${encodeURIComponent(g.a)}/${encodeURIComponent(g.b)}" onclick="RD.closeSheet()">Full head-to-head history ›</a></div>`);
}

/* =====================================================================
   League Lore: rotating fun facts
   ===================================================================== */
function buildFacts() {
  const { S, cur, CS, CAR, TM, GH, G, PG, hasLineups, inSeason, finished, HH, TRD, allDrafts, weekly, hasMed } = M;
  const F = [];
  const add = (cond, html, keys = [], tag = '') => { if (cond && html) F.push({ html, keys: [].concat(keys).filter(Boolean), tag }); };
  const who = k => `<strong>${nm(k)}</strong>`;
  const whose = k => { const n = T(k).name; return `<strong>${esc(n)}${/s$/i.test(n) ? '’' : '’s'}</strong>`; };
  const usedPairs = new Set();
  const whoAll = items => andList(items.map(x => who(x.key || x.k || x)));
  const keysOf = items => items.map(x => x.key || x.k || x);
  const yr = cur.season;
  const curGames = GH.filter(g => g.s === cur && g.type === 'reg');
  const hadGames = CS.some(r => r.n > 0);

  // ---- this season ----
  if (hadGames) {
    let t = tops(CS, r => r.pf); add(t.items.length, `${whoAll(t.items)} ${t.items.length > 1 ? 'share' : 'leads'} the league with <b>${f2(t.v)}</b> points scored in ${yr}.`, keysOf(t.items));
    t = tops(CS, r => r.pf, -1); add(t.items.length, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} the fewest points in ${yr} so far, just <b>${f2(t.v)}</b>.`, keysOf(t.items));
    t = tops(CS, r => r.pa); add(t.items.length, `Nobody has had it rougher than ${whoAll(t.items)}: <b>${f2(t.v)}</b> points scored against them in ${yr}.`, keysOf(t.items));
    t = tops(CS, r => r.pa, -1); add(t.items.length, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} faced the softest schedule in ${yr}, only <b>${f2(t.v)}</b> points against.`, keysOf(t.items));
    const best = CS[0], worst = CS[CS.length - 1];
    add(best, `${who(best.key)} owns the league's best record in ${yr} at <b>${best.w}-${best.l}</b>.`, best.key);
    add(worst && worst !== best, `${who(worst.key)} is holding down the cellar in ${yr} at <b>${worst.w}-${worst.l}</b>.`, worst.key);
    t = tops(CS, r => r.luck); add(t.v > 0.5, `${whoAll(t.items)} ${t.items.length > 1 ? 'are' : 'is'} the luckiest team in ${yr}: <b>${f(t.v)}</b> more wins than their scoring deserves.`, keysOf(t.items));
    t = tops(CS, r => r.luck, -1); add(t.v < -0.5, `Pour one out for ${whoAll(t.items)}: <b>${f(Math.abs(t.v))}</b> fewer wins than their points say they've earned in ${yr}.`, keysOf(t.items));
    t = tops(CS.filter(r => r.pp > 0), r => r.eff); add(t.items.length, `${whoAll(t.items)} ${t.items.length > 1 ? 'set' : 'sets'} the sharpest lineups in ${yr}, scoring <b>${f(t.v)}%</b> of the best possible total.`, keysOf(t.items));
    t = tops(CS.filter(r => r.pp > 0), r => r.pp - r.pf); add(t.v > 0, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} left <b>${f2(t.v)}</b> points on the bench in ${yr}. Ouch.`, keysOf(t.items));
    const W = weekly(cur);
    const WT = Object.values(W.T);
    if (WT.length) {
      t = tops(WT, x => x.cr); add(t.v > 1, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} been the week's top scorer <b>${t.v} times</b> in ${yr}.`, keysOf(t.items));
      t = tops(WT, x => x.ap / (x.apn || 1)); add(t.items.length, `If everyone played everyone each week, ${whoAll(t.items)} would be <b>${t.items[0].ap}-${t.items[0].apn - t.items[0].ap}</b> in ${yr}, the best all-play record.`, keysOf(t.items));
      if (hasMed(cur)) {
        t = tops(WT, x => x.ul); add(t.v > 0, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} lost <b>${plural(t.v, 'head-to-head game')}</b> in ${yr} despite beating the league median.`, keysOf(t.items));
        t = tops(WT, x => x.lw); add(t.v > 0, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} stolen <b>${plural(t.v, 'head-to-head win')}</b> in ${yr} with a below-median score.`, keysOf(t.items));
        t = tops(WT, x => x.mw); add(t.items.length && t.v > 0, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} beaten the median <b>${t.v} of ${t.items[0].sc.length}</b> weeks in ${yr}.`, keysOf(t.items));
      }
    }
    if (curGames.length) {
      const hi = curGames.flatMap(g => [{ k: g.a, x: g.sa, g }, { k: g.b, x: g.sb, g }]);
      t = tops(hi, x => x.x); add(t.items.length, `The top score of ${yr} so far is <b>${f2(t.v)}</b> by ${andList(t.items.map(x => `${who(x.k)} in Week ${x.g.w}`))}.`, keysOf(t.items));
      t = tops(curGames, g => g.m); add(t.items.length, `The biggest beatdown of ${yr}: ${who(t.items[0].win)} over ${who(t.items[0].lose)} by <b>${f2(t.v)}</b> in Week ${t.items[0].w}.`, [t.items[0].win, t.items[0].lose]);
      t = tops(curGames, g => g.m, -1); add(t.items.length, `Closest finish of ${yr}: ${who(t.items[0].win)} edged ${who(t.items[0].lose)} by <b>${f2(t.v)}</b> in Week ${t.items[0].w}.`, [t.items[0].win, t.items[0].lose]);
    }
    CS.forEach(r => { const c = M.curRun(r.rec); if (c && c.n >= 3 && c.c !== 'T') add(true, c.c === 'W' ? `${who(r.key)} ${pick(['is on a heater', 'is rolling', 'can\'t be stopped'])}: <b>${c.n} straight wins</b> (median games included).` : `${who(r.key)} has dropped <b>${c.n} straight</b> results (median games included). Somebody check on them.`, r.key); });
    const pw = M.PW[0]; add(pw && pw.key !== CS[0].key, `By the power rankings, ${who(pw.key)} is the real best team in ${yr}, even if the standings disagree.`, pw.key);
  }

  // ---- all-time ----
  const cars = Object.values(CAR).filter(c => c.w + c.l > 0);
  const champCount = {}; finished.forEach(s => champCount[s.champ] = (champCount[s.champ] || 0) + 1);
  let t = tops(Object.keys(champCount), k => champCount[k]);
  add(t.v > 1, `${whoAll(t.items)} ${t.items.length > 1 ? 'lead' : 'leads'} the league with <b>${t.v} championships</b>.`, t.items);
  finished.forEach(s => add(true, `${who(s.champ)} won the <b>${esc(s.season)}</b> title${s.runner ? `, beating ${who(s.runner)} in the championship` : ''}.`, [s.champ, s.runner]));
  const lastChamp = finished[finished.length - 1];
  add(lastChamp && inSeason, `${who(lastChamp && lastChamp.champ)} ${lastChamp ? `${CS.find(r => r.key === lastChamp.champ) ? `is defending the ${esc(lastChamp.season)} crown with a <b>${CS.find(r => r.key === lastChamp.champ).w}-${CS.find(r => r.key === lastChamp.champ).l}</b> record so far.` : ''}` : ''}`, lastChamp && lastChamp.champ);
  const neverWon = M.TEAMS.filter(x => !champCount[x.key] && CAR[x.key].seasons.length >= 2);
  add(neverWon.length && finished.length >= 2, `<b>${neverWon.length}</b> current managers are still chasing their first title: ${andList(neverWon.map(x => who(x.key)))}.`, neverWon.map(x => x.key));
  const runnerCount = {}; finished.forEach(s => s.runner && (runnerCount[s.runner] = (runnerCount[s.runner] || 0) + 1));
  t = tops(Object.keys(runnerCount), k => runnerCount[k]); add(t.v > 1, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} lost <b>${t.v} championship games</b>. So close, so often.`, t.items);
  t = tops(cars.filter(c => c.w + c.l >= 10), c => c.wp); add(t.items.length, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'have' : 'has'} the best all-time win rate at <b>${f(t.v * 100)}%</b>.`, t.items.map(c => c.t.key));
  t = tops(cars.filter(c => c.w + c.l >= 10), c => c.wp, -1); add(t.items.length, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'have' : 'has'} the worst all-time win rate, <b>${f(t.v * 100)}%</b>.`, t.items.map(c => c.t.key));
  t = tops(cars, c => c.pf); add(t.items.length, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'have' : 'has'} scored the most points in league history: <b>${f2(t.v)}</b>.`, t.items.map(c => c.t.key));
  t = tops(cars.filter(c => c.n >= 10), c => c.ppg); add(t.items.length, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'average' : 'averages'} a league-best <b>${f2(t.v)}</b> points per week, all time.`, t.items.map(c => c.t.key));
  t = tops(cars, c => c.apps); add(t.v > 1, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'have' : 'has'} made the playoffs <b>${t.v} times</b>, more than anyone.`, t.items.map(c => c.t.key));
  const noPO = M.TEAMS.filter(x => CAR[x.key].apps === 0 && CAR[x.key].seasons.filter(s => !s.live).length >= 2);
  noPO.forEach(x => add(true, `${who(x.key)} has never made the playoffs in <b>${CAR[x.key].seasons.filter(s => !s.live).length}</b> tries.`, x.key));
  t = tops(cars, c => c.ws); add(t.v > 3, `The longest winning run in league history belongs to ${whoAll(t.items.map(c => c.t.key))}: <b>${t.v} straight</b> (median games included).`, t.items.map(c => c.t.key));
  t = tops(cars, c => c.ls); add(t.v > 3, `${whoAll(t.items.map(c => c.t.key))} once lost <b>${t.v} straight</b> (median games included), the league's longest skid.`, t.items.map(c => c.t.key));
  t = tops(cars, c => c.hiW); add(t.v > 1, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'have' : 'has'} posted the week's top score <b>${t.v} times</b>, the most in league history.`, t.items.map(c => c.t.key));
  t = tops(cars, c => c.loW); add(t.v > 1, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'have' : 'has'} had the week's lowest score <b>${t.v} times</b>. Most in league history.`, t.items.map(c => c.t.key));
  t = tops(cars.filter(c => c.apn), c => c.ap / c.apn); add(t.items.length, `If everyone played everyone every week, ${whoAll(t.items.map(c => c.t.key))} would have the best record in league history at <b>${f(t.v * 100)}%</b>.`, t.items.map(c => c.t.key));
  t = tops(cars.filter(c => c.poW + c.poL >= 2), c => c.poW / (c.poW + c.poL)); add(t.items.length && t.v > 0, `${whoAll(t.items.map(c => c.t.key))} ${t.items.length > 1 ? 'are' : 'is'} <b>${t.items[0].poW}-${t.items[0].poL}</b> in playoff games, the best postseason record around.`, t.items.map(c => c.t.key));

  // game records
  const ptsAll = GH.flatMap(g => [{ k: g.a, x: g.sa, g }, { k: g.b, x: g.sb, g }]);
  if (GH.length) {
    t = tops(ptsAll, x => x.x); add(true, `The single-week scoring record is <b>${f2(t.v)}</b>, set by ${andList(t.items.map(x => `${who(x.k)} (${esc(x.g.y)}, ${esc(x.g.label)})`))}.`, keysOf(t.items));
    t = tops(ptsAll.filter(x => x.x > 0), x => x.x, -1); add(true, `The lowest score in league history: <b>${f2(t.v)}</b> by ${andList(t.items.map(x => `${who(x.k)} (${esc(x.g.y)}, ${esc(x.g.label)})`))}.`, keysOf(t.items));
    t = tops(GH, g => g.m); add(true, `The biggest blowout ever: ${who(t.items[0].win)} beat ${who(t.items[0].lose)} by <b>${f2(t.v)}</b> (${esc(M.gameLabel(t.items[0]))}).`, [t.items[0].win, t.items[0].lose]);
    t = tops(GH, g => g.m, -1); add(true, `The closest game ever: ${who(t.items[0].win)} ${t.v === 0 ? 'tied' : 'beat'} ${who(t.items[0].lose)} by <b>${f2(t.v)}</b> (${esc(M.gameLabel(t.items[0]))}).`, [t.items[0].win, t.items[0].lose]);
    t = tops(GH, g => g.ls); add(true, `${who(t.items[0].lose)} scored <b>${f2(t.v)}</b> and still lost to ${who(t.items[0].win)} (${esc(M.gameLabel(t.items[0]))}). The highest losing score ever.`, [t.items[0].lose, t.items[0].win]);
    t = tops(GH, g => g.ws, -1); add(true, `${who(t.items[0].win)} won with just <b>${f2(t.v)}</b> against ${who(t.items[0].lose)} (${esc(M.gameLabel(t.items[0]))}). The lowest winning score ever.`, [t.items[0].win, t.items[0].lose]);
    t = tops(GH, g => g.tot); add(true, `The highest-scoring game ever: ${who(t.items[0].a)} and ${who(t.items[0].b)} combined for <b>${f2(t.v)}</b> (${esc(M.gameLabel(t.items[0]))}).`, [t.items[0].a, t.items[0].b]);
    const finals = GH.filter(g => g.type === 'final');
    t = tops(finals, g => g.ws); add(finals.length, `The best championship-game score belongs to ${who(t.items[0] && t.items[0].win)}: <b>${f2(t.v)}</b> in ${esc(t.items[0] && t.items[0].y)}.`, t.items[0] && t.items[0].win);
  }

  // rivalries
  const pairs = [];
  M.TEAMS.forEach(a => M.TEAMS.forEach(b => { if (a.key < b.key && HH[a.key] && HH[a.key][b.key]) { const r = HH[a.key][b.key]; pairs.push({ a: a.key, b: b.key, r, n: r.w + r.l + r.t }); } }));
  const lop = pairs.filter(p => p.n >= 3).map(p => ({ ...p, d: Math.abs(p.r.w - p.r.l) })).sort((x, y) => y.d - x.d);
  lop.slice(0, 6).forEach(p => { const [hi, lo] = p.r.w >= p.r.l ? [p.a, p.b] : [p.b, p.a]; const W = Math.max(p.r.w, p.r.l), L = Math.min(p.r.w, p.r.l); if (p.d >= 2) usedPairs.add([hi, lo].sort().join('|')); add(p.d >= 2, `${who(hi)} owns ${who(lo)}: <b>${W}-${L}</b> all time head to head.`, [hi, lo], 'rival'); });
  const most = tops(pairs, p => p.n); add(most.v > 3, `${who(most.items[0].a)} and ${who(most.items[0].b)} have met <b>${most.v} times</b>, the most of any pairing. Series: ${most.items[0].r.w}-${most.items[0].r.l}.`, [most.items[0].a, most.items[0].b], 'rival');
  pairs.filter(p => p.n >= 2 && p.r.w === p.r.l).slice(0, 3).forEach(p => add(true, `${who(p.a)} vs ${who(p.b)} is dead even at <b>${p.r.w}-${p.r.l}</b>. Next one breaks the tie.`, [p.a, p.b], 'rival'));
  M.TEAMS.forEach(x => {
    const opp = Object.entries(HH[x.key] || {}).filter(([k, r]) => r.w + r.l >= 3 && T(k).current);
    if (!opp.length) return;
    const nem = opp.slice().sort((p, q) => (p[1].w / (p[1].w + p[1].l)) - (q[1].w / (q[1].w + q[1].l)) || q[1].l - p[1].l)[0];
    if (nem[1].l > nem[1].w && !usedPairs.has([x.key, nem[0]].sort().join('|'))) add(true, `${whose(x.key)} nemesis is ${who(nem[0])}: a <b>${nem[1].w}-${nem[1].l}</b> record against them.`, [x.key, nem[0]], 'rival');
  });

  // trades
  if (TRD.length) {
    const cnt = {}; TRD.forEach(x => x.keys.forEach(k => cnt[k] = (cnt[k] || 0) + 1));
    t = tops(Object.keys(cnt), k => cnt[k]); add(true, `${whoAll(t.items)} ${t.items.length > 1 ? 'have' : 'has'} made the most trades in league history: <b>${t.v}</b>.`, t.items, 'trade');
    const tp = {}; TRD.forEach(x => { const k = [...x.keys].sort().join('|'); tp[k] = (tp[k] || 0) + 1; });
    const top = Object.entries(tp).sort((a, b) => b[1] - a[1])[0];
    add(top && top[1] > 1, `Favorite trade partners: ${andList(top[0].split('|').map(who))}, with <b>${top[1]} deals</b> together.`, top[0].split('|'), 'trade');
    const quiet = M.TEAMS.filter(x => !cnt[x.key]); add(quiet.length, `${andList(quiet.map(x => who(x.key)))} ${quiet.length > 1 ? 'have' : 'has'} <b>never made a trade</b>. Hold the line.`, quiet.map(x => x.key), 'trade');
    const lastT = TRD[0]; add(lastT, `The most recent trade: ${andList(lastT.keys.map(who))} on <b>${tdate(lastT.ts)}</b>.`, lastT.keys, 'trade');
    const big = TRD.slice().sort((a, b) => (Object.keys(b.adds).length + b.picks.length) - (Object.keys(a.adds).length + a.picks.length))[0];
    const bn = Object.keys(big.adds).length + big.picks.length; add(bn >= 4, `The biggest trade ever moved <b>${bn} assets</b> between ${andList(big.keys.map(who))} (${tdate(big.ts)}).`, big.keys, 'trade');
  }
  // drafts
  allDrafts.filter(d => d.status === 'complete' && d.picks.length).forEach(d => {
    const p1 = d.picks.find(p => p.n === 1); if (!p1 || !p1.name) return;
    const k = d.s.map[p1.rid];
    add(k, `With the first pick of the <b>${d.season}</b> draft, ${who(k)} took <b>${esc(p1.name)}</b>${p1.pos ? ` (${esc(p1.pos)})` : ''}.`, k, 'draft');
  });

  // players (needs saved lineups)
  if (hasLineups) {
    const pg = PG.filter(p => p.pts > 0);
    t = tops(pg, p => p.pts); add(t.items.length, `The best single-player game in league history: <b>${esc(M.pname(t.items[0].pid))}</b> put up <b>${f2(t.v)}</b> for ${who(t.items[0].k)} (${esc(M.gameLabel(t.items[0].g))}).`, keysOf(t.items), 'player');
    const curPG = pg.filter(p => p.g.s === cur);
    t = tops(curPG, p => p.pts); add(t.items.length, `Best player game of ${yr}: <b>${esc(M.pname(t.items[0] && t.items[0].pid))}</b> with <b>${f2(t.v)}</b> for ${who(t.items[0] && t.items[0].k)} in Week ${t.items[0] && t.items[0].g.w}.`, keysOf(t.items), 'player');
    const tot = {}; PG.forEach(p => { const id = p.k + '|' + p.pid; (tot[id] || (tot[id] = { k: p.k, pid: p.pid, pts: 0, n: 0 })); tot[id].pts += p.pts; tot[id].n++; });
    const TT = Object.values(tot);
    t = tops(TT, x => x.pts); add(t.items.length, `<b>${esc(M.pname(t.items[0].pid))}</b> has scored <b>${f2(t.v)}</b> points as a starter for ${who(t.items[0].k)}, the most by any player for one team.`, t.items[0].k, 'player');
    t = tops(TT, x => x.n); add(t.items.length, `${who(t.items[0].k)} has started <b>${esc(M.pname(t.items[0].pid))}</b> <b>${t.v} times</b>, the league's most loyal lineup slot.`, t.items[0].k, 'player');
    const dud = PG.filter(p => p.pts <= 0 && p.g.type !== 'reg'); add(dud.length, `${who(dud[0] && dud[0].k)} started <b>${esc(M.pname(dud[0] && dud[0].pid))}</b> in a playoff game and got <b>${f2(dud[0] && dud[0].pts)}</b> points.`, dud[0] && dud[0].k, 'player');
    M.TEAMS.forEach(x => {
      const mine = TT.filter(y => y.k === x.key).sort((a, b) => b.pts - a.pts)[0];
      if (mine) add(true, `${whose(x.key)} all-time MVP is <b>${esc(M.pname(mine.pid))}</b>: <b>${f2(mine.pts)}</b> points across ${plural(mine.n, 'start')}.`, x.key, 'player');
    });
  }
  return F;
}

/* Rotating card: auto-advances, tap or swipe for the next fact, pauses on hover
   and while the tab is hidden. Easter eggs from eggs.js show up now and then. */
function loreCard(id, facts, { title = 'League Lore', ms = 9000 } = {}) {
  if (!facts.length) return '';
  setTimeout(() => startLore(id, facts, ms), 0);
  return `<section class="glass lore rise" id="${id}" aria-roledescription="carousel" aria-label="${esc(title)}">
    <div class="lore-in"><div class="lore-top"><div class="eyebrow"><span aria-hidden="true">✦</span> <span class="lore-h">${esc(title)}</span></div>
    <div class="lore-ctl"><button type="button" data-a="prev" aria-label="Previous fact">‹</button><button type="button" data-a="next" aria-label="Next fact">›</button></div></div>
    <div class="lore-box"><div class="lore-text" aria-live="polite"></div></div>
    <div class="lore-foot"><span>Tap for another</span><span class="lore-n"></span></div></div><div class="lore-prog" style="--lore-ms:${ms}ms"></div></section>`;
}
const loreTimers = {};
function startLore(id, facts, ms) {
  const el = document.getElementById(id); if (!el) return;
  clearTimeout(loreTimers[id]);
  const eggs = (window.LEAGUE_EGGS || []).filter(Boolean);
  const chance = Number(window.LEAGUE_EGG_CHANCE) || 0;
  let deck = [], hist = [], pos = -1, paused = false, timer = null;
  const draw = () => {
    if (eggs.length && Math.random() < chance) return { html: pick(eggs), egg: true };
    if (!deck.length) { deck = facts.slice(); for (let i = deck.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [deck[i], deck[j]] = [deck[j], deck[i]]; } }
    return deck.pop();
  };
  const txt = $('.lore-text', el), box = $('.lore-box', el), prog = $('.lore-prog', el), cnt = $('.lore-n', el);
  const show = (fct, instant) => {
    const paint = () => { txt.innerHTML = fct.html; box.classList.toggle('egg', !!fct.egg); txt.classList.remove('out'); cnt.textContent = fct.egg ? '★' : `${facts.length} facts`; };
    if (instant) paint(); else { txt.classList.add('out'); setTimeout(paint, 230); }
    prog.classList.remove('run'); void prog.offsetWidth; prog.classList.add('run');
    clearTimeout(timer); timer = loreTimers[id] = setTimeout(next, ms);
  };
  const next = force => { if (!document.getElementById(id)) return; if (!force && (paused || document.hidden)) { timer = loreTimers[id] = setTimeout(next, 1000); return; } pos++; if (pos >= hist.length) hist.push(draw()); show(hist[pos]); };
  const prev = () => { if (pos > 0) { pos--; show(hist[pos]); } };
  el.addEventListener('click', e => { const a = e.target.closest('button') && e.target.closest('button').dataset.a; if (a === 'prev') prev(); else next(true); });
  const canHover = matchMedia('(hover: hover) and (pointer: fine)').matches;
  if (canHover) el.addEventListener('mouseenter', () => { paused = true; el.classList.add('paused'); });
  el.addEventListener('mouseleave', () => { paused = false; el.classList.remove('paused'); });
  let x0 = null;
  el.addEventListener('touchstart', e => { x0 = e.touches[0].clientX; }, { passive: true });
  el.addEventListener('touchend', e => { if (x0 == null) return; const dx = e.changedTouches[0].clientX - x0; x0 = null; if (dx > 40) { e.preventDefault(); prev(); } else if (dx < -40) { e.preventDefault(); next(true); } });
  pos = 0; hist.push(draw()); show(hist[0], true);
}

/* =====================================================================
   Pages
   ===================================================================== */
const P = {};

/* ---------- HOME ---------- */
P.home = function (args) {
  const { cur, inSeason, nowW, scoredWeeks, liveWeek, CS, CSM, hasMed, ps, WK, finished, nextWk, cutN } = M;
  const n = Number(args[0]) && scoredWeeks.includes(Number(args[0])) ? Number(args[0]) : (liveWeek || scoredWeeks[scoredWeeks.length - 1]);
  const lastChamp = finished[finished.length - 1];
  let h = `<section class="glass hero rise"><div class="hero-main"><div class="eyebrow">${esc(cur.season)} season${inSeason ? ` · Week ${nowW}` : ''}</div><div class="hero-name">${esc(M.leagueName)}</div>
    <div class="hero-sub">${liveWeek ? '<span class="badge live"><span class="pulse"></span> Live</span>' : ''}<span class="badge">${M.TEAMS.length} teams</span><span class="badge">${cur.settings.playoff_teams || 6} make playoffs</span>${hasMed(cur) ? '<span class="badge">Median game</span>' : ''}${lastChamp ? `<a class="badge gold" href="#/team/${encodeURIComponent(lastChamp.champ)}">🏆 ${esc(lastChamp.season)} champ: ${nm(lastChamp.champ)}</a>` : ''}</div></div></section><div class="gap"></div>`;
  h += loreCard('lore-home', FACTS) + '<div class="gap"></div>';
  if (!n) return h + card('This week', `<div class="empty">The ${esc(cur.season)} season hasn't started yet. Check back once Week 1 is played.</div>`);
  const W = WK[cur.season][n];
  const live = n === liveWeek, po = n >= ps(cur), m = hasMed(cur) && !po;
  const games = W.games, sc = W.sc, medv = W.md;
  const rows = Object.keys(sc).map(k => { const g = games.find(x => x.a === k || x.b === k), o = g.a === k ? g.b : g.a, os = g.a === k ? g.sb : g.sa, s = sc[k], won = s > os, ab = m && s > medv; return { k, s, o, os, won, tie: s === os, ab, tot: (won ? 1 : 0) + (ab ? 1 : 0) }; }).sort((a, b) => b.s - a.s);
  const idle = r => live && r.s === 0 && r.os === 0;
  const opts = scoredWeeks.slice().reverse().map(k => [k, `Wk ${k}${k === liveWeek ? ' •' : ''}`]);
  const gid = g => (W.gids || []).find(id => M.G[id].a === g.a && M.G[id].b === g.b);
  const muCard = g => {
    const tot = g.sa + g.sb, pa = tot ? g.sa / tot * 100 : 50, done = !live, id = gid(g);
    const side = (k, s, o) => `<div class="mu-side ${done && s > o ? 'won' : done && s < o ? 'lose' : ''}">${tm(k, { sub: false, size: 'sm', link: id == null })}<span class="sb">${f2(s)}</span></div>`;
    const status = g.sa === g.sb ? (live ? 'Even' : 'Tied') : `${nm(g.sa > g.sb ? g.a : g.b)} ${live ? 'leads' : 'won'} by ${f2(Math.abs(g.sa - g.sb))}`;
    return `<div class="mu${(g.a === ME || g.b === ME) ? ' is-lead' : ''}${id != null ? ' tap' : ''}"${id != null ? ` onclick="if(!event.target.closest('a'))RD.openGame(${id})"` : ''}>${side(g.a, g.sa, g.sb)}${side(g.b, g.sb, g.sa)}<div class="mu-meter"><i style="width:${pa}%;background:${g.sa >= g.sb ? 'var(--gold)' : 'rgba(255,255,255,.28)'}"></i><i style="width:${100 - pa}%;background:${g.sb > g.sa ? 'var(--gold)' : 'rgba(255,255,255,.28)'}"></i></div><div class="mu-foot"><span>${status}</span>${id != null ? '<span class="chev">Lineups</span>' : live ? '<span class="badge live"><span class="pulse"></span> Live</span>' : ''}</div></div>`;
  };
  h += `<div class="seg-row rise">${seg('home-week', opts, n, 'RD.homeWeek')}</div>`;
  // Your week
  if (ME && sc[ME] != null) {
    const r = rows.find(x => x.k === ME), rk = rows.indexOf(r) + 1;
    h += card(`Your week · ${nm(ME)}`, `<div class="stat-row" style="--n:${m ? 4 : 3};border-radius:12px;border:1px solid var(--line)"><div><div class="sv">${f2(r.s)}</div><div class="sl">Score</div></div><div><div class="sv">${ord(rk)}</div><div class="sl">of ${rows.length} this week</div></div><div><div class="sv ${r.won ? 'win' : r.tie ? '' : 'loss'}">${r.tie ? 'T' : r.won ? (live ? 'Up' : 'W') : (live ? 'Down' : 'L')}</div><div class="sl">vs ${nm(r.o)}</div></div>${m ? `<div><div class="sv ${r.ab ? 'win' : 'loss'}">${sg(r.s - medv, 1)}</div><div class="sl">vs median</div></div>` : ''}</div>`, { cls: 'is-lead' }) + '<div class="gap"></div>';
  }
  h += card(`Week ${n} matchups`, `<div class="mus">${games.map(muCard).join('')}</div>`, { right: live ? '<span class="badge live"><span class="pulse"></span> In progress</span>' : po ? '<span class="badge gold">Playoffs</span>' : '<span class="badge">Final</span>', note: live ? 'Games are still being played, so scores will change.' : 'Tap a matchup to see both starting lineups.' });
  h += '<div class="gap"></div>';
  // Median watch
  if (rows.length) {
    const hmx = Math.max(...rows.map(r => r.s), 1);
    const chip = r => idle(r) ? '<span class="dim">–</span>' : `<span class="chip c${r.tot}">${r.tot}-${2 - r.tot}</span>`;
    const body = `<div class="rows">${rows.map((r, i) => `<a class="row${i === 0 ? ' top' : ''}${meCls(r.k)}" href="#/team/${encodeURIComponent(r.k)}" style="grid-template-columns:24px minmax(0,1fr) auto"><span class="rk">${i + 1}</span><span style="min-width:0;display:grid;gap:6px">${tm(r.k, { sub: false, size: 'sm', link: false })}<span class="bar"><i style="width:${r.s / hmx * 100}%"></i>${m ? `<span class="mk" style="left:${medv / hmx * 100}%"></span>` : ''}</span></span><span class="rv"><span class="v">${f2(r.s)}</span><span class="s">${m ? `<span class="${cls(r.s - medv)}">${sg(r.s - medv)}</span> ${chip(r)}` : (r.won ? '<span class="win">W</span>' : '<span class="loss">L</span>')}</span></span></a>`).join('')}</div>`;
    h += card(m ? 'Median watch' : 'Scoreboard', body, { note: m ? `Every team also plays the league median each week. Median line: <b class="gold">${f2(medv)}</b>${live ? ' (moves until games finish)' : ''}. The chip is the week's record out of 2.` : '' });
    h += '<div class="gap"></div>';
    // highlights
    const mg = g => Math.abs(g.sa - g.sb), cl = games.reduce((a, b) => mg(b) < mg(a) ? b : a), bl = games.reduce((a, b) => mg(b) > mg(a) ? b : a), lead = g => g.sa >= g.sb ? g.a : g.b;
    const nl = a => a.length ? a.map(r => nm(r.k)).join(', ') : 'Nobody';
    const hs = [['🔥 Top score', nm(rows[0].k), f2(rows[0].s) + ' pts'], live ? (rows.some(r => r.s === 0) ? ['⏳ Yet to score', nl(rows.filter(r => r.s === 0)), "Haven't scored a point yet"] : ['🐢 Lowest so far', nm(rows[rows.length - 1].k), f2(rows[rows.length - 1].s) + ' pts']) : ['🧯 Lowest score', nm(rows[rows.length - 1].k), f2(rows[rows.length - 1].s) + ' pts']];
    hs.push([live ? '🔨 Biggest lead' : '🔨 Biggest blowout', nm(lead(bl)), (live ? 'Ahead by ' : 'Won by ') + f2(mg(bl))], [live ? '😬 Closest right now' : '😬 Closest game', cl.sa === cl.sb ? `${nm(cl.a)} vs ${nm(cl.b)}` : nm(lead(cl)), cl.sa === cl.sb ? 'Level' : (live ? 'Ahead by ' : 'Won by ') + f2(mg(cl))]);
    if (m) {
      hs.push([live ? '✅ Winning both' : '✅ Went 2-0', nl(rows.filter(r => r.tot === 2 && !idle(r))), 'Head-to-head and median']);
      if (!live) hs.push(['❌ Went 0-2', nl(rows.filter(r => r.tot === 0)), 'Head-to-head and median'], ['🍀 Lucky win', nl(rows.filter(r => r.won && !r.ab)), 'Won with a below-median score'], ['😭 Unlucky loss', nl(rows.filter(r => !r.won && r.ab)), 'Lost with an above-median score']);
    }
    if (M.hasLineups && !live) {
      const pl = Object.entries(W.lu).flatMap(([k, l]) => l.map(([pid, pts]) => ({ k, pid, pts }))).sort((a, b) => b.pts - a.pts)[0];
      if (pl) hs.push(['⭐ Player of the week', esc(M.pname(pl.pid)), `${f2(pl.pts)} pts for ${nm(pl.k)}`]);
    }
    h += card('Week highlights', tiles(hs));
  }
  // next up
  if (nextWk && (n === liveWeek || n === scoredWeeks[scoredWeeks.length - 1]) && nextWk.games.length) {
    h += '<div class="gap"></div>' + card(`Next up · Week ${nextWk.w}`, `<div class="mus">${nextWk.games.map(g => { const r = M.hh(g.a, g.b); return `<a class="mu tap${(g.a === ME || g.b === ME) ? ' is-lead' : ''}" href="#/h2h/${encodeURIComponent(g.a)}/${encodeURIComponent(g.b)}">${[g.a, g.b].map(k => `<div class="mu-side">${tm(k, { sub: false, size: 'sm', link: false })}<span class="dim tn" style="font-size:.8rem">${CSM[k] ? CSM[k].w + '-' + CSM[k].l : ''}</span></div>`).join('')}<div class="mu-foot"><span>All-time: ${r.w + r.l ? `${nm(g.a)} ${r.w}-${r.l}` : 'first meeting'}</span><span class="chev">History</span></div></a>`; }).join('')}</div>`);
  }
  // standings snapshot
  const std = CS;
  h += '<div class="gap"></div>' + card(`Standings${M.lastFinal ? ` after Week ${M.lastFinal}` : ''}`, standingsRows(std, cutN, true), { right: '<a class="r" href="#/standings">Full standings ›</a>' });
  return h;
};
function standingsRows(std, cutN, compact) {
  return `<div class="rows">${std.map((t, i) => `${i === cutN && i < std.length ? '<div class="cutline">Playoff line</div>' : ''}<a class="row${i === 0 ? ' top' : ''}${meCls(t.key)}" href="#/team/${encodeURIComponent(t.key)}"><span class="rk">${i + 1}</span>${tm(t.key, { link: false })}<span class="rv"><span class="v">${t.w}-${t.l}</span><span class="s">${f(t.pf)} PF${compact ? '' : ''}</span></span></a>`).join('')}</div>`;
}

/* ---------- STANDINGS ---------- */
P.standings = function (args) {
  const { S, cur, SS, inSeason, hasMed, regW, ps, REC } = M;
  const s = S.find(x => String(x.season) === String(args[0])) || cur;
  const std = SS[s.season], cutN = s.settings.playoff_teams || 6, isCur = s === cur && inSeason;
  let h = pageHead('Standings', `${esc(s.season)} standings`, isCur ? `Through Week ${M.lastFinal}` : s.champ ? `Champion: ${nm(s.champ)}` : '');
  h += `<div class="seg-row rise">${seg('std-yr', S.slice().reverse().map(x => [x.season, x.season]), s.season, 'RD.stdYear')}</div>`;
  // playoff race
  const tot = regW(s) * (hasMed(s) ? 2 : 1);
  const left = std.map(t => tot - t.n);
  const lineW = std[cutN - 1] ? std[cutN - 1].w : 0, firstOut = std[cutN] ? std[cutN].w : 0;
  const status = (t, i) => {
    if (!isCur) return s.champ === t.key ? '<span class="badge gold">🏆 Champion</span>' : s.place[t.key] ? `<span class="badge">${ord(s.place[t.key])}</span>` : s.inPO.has(t.key) ? '<span class="badge">Playoffs</span>' : '';
    const rem = left[i];
    if (i < cutN && t.w > firstOut + (std[cutN] ? left[cutN] : 0)) return '<span class="badge win">Clinched</span>';
    if (i >= cutN && t.w + rem < lineW) return '<span class="badge loss">Eliminated</span>';
    return i < cutN ? '' : `<span class="badge">${lineW - t.w} back</span>`;
  };
  const rows = `<div class="rows">${std.map((t, i) => `${i === cutN ? '<div class="cutline">Playoff line</div>' : ''}<a class="row${i === 0 ? ' top' : ''}${meCls(t.key)}" href="#/team/${encodeURIComponent(t.key)}"><span class="rk">${i + 1}</span><span style="min-width:0;display:grid;gap:5px">${tm(t.key, { link: false })}<span style="display:flex;gap:6px;align-items:center;flex-wrap:wrap">${dots(t.rec.slice(-12))}${status(t, i)}</span></span><span class="rv"><span class="v">${t.w}-${t.l}${t.t ? '-' + t.t : ''}</span><span class="s">${f(t.pf)} PF · ${f(t.pa)} PA</span></span></a>`).join('')}</div>`;
  h += card('Standings', rows, { note: `${hasMed(s) ? 'Records count two results a week: the head-to-head game and the league median. ' : ''}The squares are the most recent results, newest on the right.` });
  h += '<div class="gap"></div>' + card('All the numbers', table(['#', 'Team', 'W-L', 'PF', 'PA', 'Diff', 'PF/Wk', 'Max PF', 'Eff.', isCur ? 'Pace' : 'Luck'], std.map((t, i) => [i + 1, tm(t.key, { sub: false, size: 'sm' }), `${t.w}-${t.l}`, f(t.pf), f(t.pa), `<span class="${cls(t.diff)}">${sg(t.diff)}</span>`, f(t.ppg), f(t.pp), f(t.eff) + '%', isCur ? f0(t.proj) + '/' + tot : `<span class="${cls(t.luck)}">${sg(t.luck)}</span>`]), { cut: cutN - 1, rowCls: i => meCls(std[i].key) }), { note: isCur ? 'Pace = this record projected over the full regular season.' : 'Luck = actual wins minus the wins expected from points scored and allowed.' });
  h += bracketCard(s);
  return h;
};
function bracketCard(s) {
  const B = (s.bracket || []).slice(); if (!B.length) return '';
  const side = (t, fr, m) => t != null ? `<div class="mu-side ${m.w != null ? (m.w === t ? 'won' : 'lose') : ''}">${tm(s.map[t], { sub: false, size: 'sm' })}${m.w === t ? '<span class="badge gold">Won</span>' : ''}</div>` : `<div class="mu-side"><span class="dim" style="font-size:.82rem">${fr ? `${fr.w != null ? 'Winner' : 'Loser'} of game ${fr.w != null ? fr.w : fr.l}` : 'TBD'}</span></div>`;
  B.sort((a, b) => a.r - b.r || (a.p || 0) - (b.p || 0) || a.m - b.m);
  const decided = B.some(m => m.w != null);
  const rounds = [...new Set(B.map(m => m.r))];
  return '<div class="gap"></div>' + card(decided ? 'Playoff bracket' : 'Projected playoff bracket', rounds.map(r => `<div class="eyebrow" style="margin:${r === rounds[0] ? 0 : 14}px 0 8px">Round ${r} · Week ${M.ps(s) + r - 1}</div><div class="mus">${B.filter(m => m.r === r).map(m => `<div class="mu${m.p === 1 ? ' is-lead' : ''}"><div class="mu-foot" style="margin:-2px 0 2px"><span>${esc(m.p === 1 ? '🏆 Championship' : m.p ? ord(m.p) + ' place game' : 'Game ' + m.m)}</span></div>${side(m.t1, m.t1_from, m)}${side(m.t2, m.t2_from, m)}</div>`).join('')}</div>`).join(''), { note: decided ? '' : `If the season ended today. Playoffs start Week ${M.ps(s)}.` });
}

/* ---------- POWER & LUCK ---------- */
P.power = function () {
  const { CS, PW, cur, S, SS, TEAMS, REC, runs, curRun } = M;
  const std = CS;
  let h = pageHead('Power & luck', 'Power rankings', `${esc(cur.season)} season`);
  const mxp = Math.max(...PW.map(t => t.pow)), mnp = Math.min(...PW.map(t => t.pow));
  h += card('Power rankings', `<div class="rows">${PW.map((t, i) => { const d = std.findIndex(x => x.key === t.key) - i; return `<a class="row${i === 0 ? ' top' : ''}${meCls(t.key)}" href="#/team/${encodeURIComponent(t.key)}"><span class="rk">${i + 1}</span><span style="min-width:0;display:grid;gap:6px">${tm(t.key, { sub: false, link: false })}<span class="bar"><i style="width:${8 + (t.pow - mnp) / ((mxp - mnp) || 1) * 92}%"></i></span></span><span class="rv"><span class="v gold">${f(t.pow, 2)}</span><span class="s">${d > 0 ? `<span class="win">▲${d}</span>` : d < 0 ? `<span class="loss">▼${-d}</span>` : '–'} vs standings</span></span></a>`; }).join('')}</div>`, { note: 'A blend of scoring (40%), win % (25%), expected wins from scoring (20%) and lineup efficiency (15%).' });
  h += '<div class="gap"></div><div class="two">';
  h += card('Luck index', `<div class="rows">${CS.slice().sort((a, b) => b.luck - a.luck).map((t, i) => `<div class="row${meCls(t.key)}"><span class="rk">${i + 1}</span>${tm(t.key, { sub: false, size: 'sm' })}<span class="rv"><span class="v ${cls(t.luck)}">${sg(t.luck)}</span><span class="s">${t.w} W vs ${f(t.xw)} expected</span></span></div>`).join('')}</div>`, { note: 'Actual wins minus the wins expected from points scored and allowed.' });
  h += card('Lineup efficiency', `<div class="rows">${CS.slice().sort((a, b) => b.eff - a.eff).map((t, i) => `<div class="row${meCls(t.key)}"><span class="rk">${i + 1}</span><span style="min-width:0;display:grid;gap:6px">${tm(t.key, { sub: false, size: 'sm' })}<span class="bar"><i style="width:${t.eff}%"></i></span></span><span class="rv"><span class="v">${f(t.eff)}%</span><span class="s loss">${f(t.pp - t.pf)} on bench</span></span></div>`).join('')}</div>`, { note: 'Points scored as a share of the best possible lineup each week.' });
  h += '</div><div class="gap"></div>';
  // matchup map
  const lgPA = mean(CS.map(t => t.pag)), lgPF = mean(CS.map(t => t.ppg));
  const xs = CS.map(t => t.ppg), ys = CS.map(t => t.pag), x0 = Math.min(...xs) - 6, x1 = Math.max(...xs) + 6, y0 = Math.min(...ys) - 6, y1 = Math.max(...ys) + 6;
  const px = v => 46 + (v - x0) / ((x1 - x0) || 1) * 440, py = v => 16 + (v - y0) / ((y1 - y0) || 1) * 270;
  const svg = `<svg viewBox="0 0 500 330" width="100%" role="img" aria-label="Points scored per week against points allowed per week"><rect x="46" y="16" width="440" height="270" rx="10" fill="rgba(255,255,255,.02)" stroke="rgba(255,255,255,.08)"/>
    <line x1="${px(lgPF)}" y1="16" x2="${px(lgPF)}" y2="286" stroke="#D4B46A" stroke-dasharray="4 4" opacity=".45"/><line x1="46" y1="${py(lgPA)}" x2="486" y2="${py(lgPA)}" stroke="#D4B46A" stroke-dasharray="4 4" opacity=".45"/>
    <text x="54" y="32" font-size="11" opacity=".45">Soft schedule, low scoring</text><text x="478" y="32" font-size="11" text-anchor="end" opacity=".45">Soft schedule, high scoring</text>
    <text x="54" y="278" font-size="11" opacity=".45">Tough schedule, low scoring</text><text x="478" y="278" font-size="11" text-anchor="end" opacity=".45">Tough schedule, high scoring</text>
    <text x="266" y="314" font-size="12" text-anchor="middle" opacity=".7">Points scored per week →</text><text x="14" y="150" font-size="12" transform="rotate(-90 14 150)" text-anchor="middle" opacity=".7">Points against per week →</text>
    ${CS.map(t => `<g><circle cx="${px(t.ppg)}" cy="${py(t.pag)}" r="16" fill="#D4B46A" fill-opacity="${.12 + t.wp * .6}" stroke="${t.key === ME ? '#fff' : '#D4B46A'}" stroke-width="${t.key === ME ? 2 : 1}"/><text x="${px(t.ppg)}" y="${py(t.pag) + 4}" font-size="10.5" font-weight="800" text-anchor="middle">${esc(T(t.key).code)}</text></g>`).join('')}</svg>`;
  h += card('Matchup map', svg + `<div class="legend">${CS.map(t => `<span><b>${esc(T(t.key).code)}</b> ${nm(t.key)}</span>`).join('')}</div>`, { note: 'Bottom right is the sweet spot: scoring a lot against a tough schedule. Brighter circles have better win %. Dashed lines are league averages.' });
  h += '<div class="gap"></div>';
  h += card('Strength of schedule', table(['#', 'Team', 'PA/Wk', 'vs Avg', 'Margin/Wk'], CS.slice().sort((a, b) => b.pag - a.pag).map((t, i) => [i + 1, tm(t.key, { sub: false, size: 'sm' }), f(t.pag), `<span class="${cls(-(t.pag - lgPA))}">${sg(t.pag - lgPA)}</span>`, `<span class="${cls(t.diff)}">${sg(t.wk ? t.diff / t.wk : 0)}</span>`]), { rowCls: () => '' }), { note: 'Points opponents score against each team, per week. Higher = tougher opponents.' });
  h += '<div class="gap"></div>';
  h += card('Streaks', table(['Team', '', 'Now', 'Best run', 'Worst run', `${esc(cur.season)} best`, `${esc(cur.season)} worst`], M.TEAMS.slice().sort((a, b) => runs(REC[b.key], 'W') - runs(REC[a.key], 'W')).map(t => { const c = curRun(REC[t.key]); const r = (CS.find(x => x.key === t.key) || {}).rec || ''; return [av(t.key, 'sm'), `<a href="#/team/${encodeURIComponent(t.key)}"><b>${nm(t.key)}</b></a>`, c ? `<span class="${c.c === 'W' ? 'win' : 'loss'}">${c.c}${c.n}</span>` : '–', runs(REC[t.key], 'W'), runs(REC[t.key], 'L'), runs(r, 'W'), runs(r, 'L')]; }), { left: 2 }), { note: 'Every result across every season, median games included.' });
  const prev = S[S.length - 2];
  if (prev) {
    const PS = SS[prev.season];
    const rows = CS.map(t => { const p = PS.find(x => x.key === t.key); return { t, p, d: p && p.wk ? t.ppg - p.ppg : null }; }).filter(x => x.d != null).sort((a, b) => b.d - a.d);
    h += '<div class="gap"></div>' + card('Season over season', table(['#', 'Team', `${esc(prev.season)} PF/Wk`, `${esc(cur.season)} PF/Wk`, 'Change'], rows.map((x, i) => [i + 1, tm(x.t.key, { sub: false, size: 'sm' }), f(x.p.ppg), f(x.t.ppg), `<b class="${cls(x.d)}">${sg(x.d)}</b>`])));
  }
  return h;
};

/* ---------- WEEKLY ---------- */
P.weekly = function (args) {
  const { S, weekly, hasMed } = M;
  const seasons = S.filter(s => weekly(s).wks.length).reverse();
  let h = pageHead('Weekly', 'Week by week');
  if (!seasons.length) return h + card('', '<div class="empty">No finished weeks yet.</div>');
  const s = seasons.find(x => String(x.season) === String(args[0])) || seasons[0];
  const W = weekly(s), TT = Object.values(W.T), m = hasMed(s);
  h += `<div class="seg-row rise">${seg('wk-yr', seasons.map(x => [x.season, x.season]), s.season, 'RD.weeklyYear')}</div>`;
  const all = []; TT.forEach(t => t.sc.forEach((x, i) => all.push({ k: t.k, w: t.wks[i], x })));
  const G = M.GH.filter(g => g.s === s && g.type === 'reg');
  const hi = tops(all, x => x.x).items[0], lo = tops(all, x => x.x, -1).items[0], bl = tops(G, g => g.m).items[0], cl = tops(G, g => g.m, -1).items[0], lt = tops(G, g => g.ls).items[0], wl = tops(G, g => g.ws, -1).items[0];
  h += card('Season superlatives', tiles([['💥 Highest score', nm(hi.k), `${f2(hi.x)} pts, Week ${hi.w}`], ['🧯 Lowest score', nm(lo.k), `${f2(lo.x)} pts, Week ${lo.w}`], ['🔨 Biggest blowout', nm(bl.win), `Beat ${nm(bl.lose)} by ${f2(bl.m)} (Wk ${bl.w})`, `RD.openGame(${bl.id})`], ['😬 Closest game', nm(cl.win), `Edged ${nm(cl.lose)} by ${f2(cl.m)} (Wk ${cl.w})`, `RD.openGame(${cl.id})`], ['😭 Most points in a loss', nm(lt.lose), `${f2(lt.ls)} pts, lost to ${nm(lt.win)}`, `RD.openGame(${lt.id})`], ['🍀 Fewest points in a win', nm(wl.win), `${f2(wl.ws)} pts, beat ${nm(wl.lose)}`, `RD.openGame(${wl.id})`]]));
  h += '<div class="gap"></div>';
  const hl = (x, i) => x === W.wks[i].mx ? `<b class="gold">${f2(x)}</b>` : x === W.wks[i].mn ? `<span class="loss">${f2(x)}</span>` : f2(x);
  h += card('Weekly scores', table(['', 'Team', ...W.wks.map(w => 'Wk ' + w.w), 'Avg', '±', 'Top wk'], TT.slice().sort((a, b) => b.avg - a.avg).map(t => [av(t.k, 'sm'), `<a href="#/team/${encodeURIComponent(t.k)}"><b>${nm(t.k)}</b></a>`, ...t.sc.map(hl), `<b>${f2(t.avg)}</b>`, f(t.sd), t.cr || '–']).concat(m ? [['', '<span class="dim">League median</span>', ...W.wks.map(w => `<span class="dim">${f2(w.md)}</span>`), '', '', '']] : []), { left: 2 }), { note: `Gold = the week's top score, red = the lowest. ± is the week-to-week swing (standard deviation).` });
  h += '<div class="gap"></div>';
  if (m) h += card('How the wins were earned', table(['', 'Team', 'Head-to-head', 'Vs median', 'All-play', 'Lucky W', 'Unlucky L'], TT.slice().sort((a, b) => b.ap - a.ap).map(t => [av(t.k, 'sm'), `<b>${nm(t.k)}</b>`, `${t.hw}-${t.hl}`, `${t.mw}-${t.ml}`, `${t.ap}-${t.apn - t.ap}`, t.lw ? `<span class="win">${t.lw}</span>` : '–', t.ul ? `<span class="loss">${t.ul}</span>` : '–']), { left: 2 }), { note: 'All-play is your record if you had played every other team every week. Lucky wins came with a below-median score; unlucky losses came with an above-median score.' }) + '<div class="gap"></div>';
  h += card('Every game', W.wks.slice().reverse().map(w => `<div class="eyebrow" style="margin:14px 0 2px">Week ${w.w}</div>${G.filter(g => g.w === w.w).sort((a, b) => b.m - a.m).map(gameLine).join('')}`).join('').replace('margin:14px', 'margin:0'));
  return h;
};
function gameLine(g, persp) {
  const left = persp ? (g.a === persp ? g.a : g.b) : g.win, right = left === g.a ? g.b : g.a;
  const ls = left === g.a ? g.sa : g.sb, rs = left === g.a ? g.sb : g.sa;
  const res = ls > rs ? 'W' : ls < rs ? 'L' : 'T';
  return `<div class="gl tap${persp ? (res === 'W' ? ' is-win' : res === 'L' ? ' is-loss' : '') : ''}" onclick="RD.openGame(${g.id})"><span class="w">${persp ? res : esc(String(g.y).slice(2) === String(M.cur.season).slice(2) ? 'Wk ' + g.w : "'" + String(g.y).slice(2))}</span><span style="min-width:0;display:grid;gap:3px"><span class="tm-n" style="font-size:.86rem">${persp ? `<span class="dim">vs</span> ${nm(right)}` : `${nm(left)} <span class="dim">vs</span> ${nm(right)}`}</span><span class="dim" style="font-size:.7rem">${esc(M.gameLabel(g))} · ${g.tie ? 'tied' : `by ${f2(g.m)}`}</span></span><span class="sc">${f2(ls)}<span class="dim">–</span>${f2(rs)}</span></div>`;
}

/* ---------- MANAGERS ---------- */
P.teams = function () {
  let h = pageHead('Managers', 'The league');
  const cur = M.TEAMS.map(t => t.key), past = Object.keys(M.TM).filter(k => !M.TM[k].current);
  const tc = k => { const c = M.CAR[k]; return `<a class="team-card tap${meCls(k)}" href="#/team/${encodeURIComponent(k)}">${av(k, 'lg')}<span class="tm-t" style="flex:1"><span class="tm-n" style="font-size:1rem">${nm(k)}</span><span class="tm-u">${esc(T(k).user)} · ${c.w}-${c.l} all time</span><span class="trophies">${c.titles.map(y => `<span class="badge gold">🏆 ${esc(y)}</span>`).join('')}${c.apps ? `<span class="badge">${plural(c.apps, 'playoff trip')}</span>` : ''}</span></span><span class="chev"></span></a>`; };
  h += card('', `<div class="team-grid">${cur.map(tc).join('')}</div>`);
  if (past.length) h += '<div class="gap"></div>' + card('Former managers', `<div class="team-grid">${past.map(tc).join('')}</div>`);
  return h;
};
P.team = function (args) {
  const k = decodeURIComponent(args[0] || '');
  if (!M.TM[k]) return P.teams();
  const tab = ['overview', 'games', 'rivals', 'players', 'moves'].includes(args[1]) ? args[1] : 'overview';
  const t = T(k), c = M.CAR[k], { cur, CSM, inSeason } = M;
  const curR = CSM[k];
  let h = `<div class="picker rise">${teamSelect('team-pick', k, 'RD.go(\'team/\'+encodeURIComponent(this.value)+\'/' + tab + '\')')}<button class="share" type="button" onclick="RD.share()" aria-label="Share this page"><svg class="share-ic" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3v13M7 8l5-5 5 5M5 14v5a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2v-5"/></svg>Share</button></div>`;
  h += `<section class="glass fhero hero rise"><div class="fhero-main">${av(k, 'xl')}<div style="min-width:0"><div class="eyebrow">${t.current ? (curR ? `${esc(cur.season)}: ${curR.w}-${curR.l} · ${ord(curR.rank)} place` : 'Manager') : 'Former manager'}</div><div class="fhero-name">${nm(k)}</div><div class="fhero-sub">${esc(t.user)} · ${plural(c.seasons.length, 'season')} (${esc(c.seasons[0].y)}${c.seasons.length > 1 ? '–' + esc(c.seasons[c.seasons.length - 1].y) : ''})</div><div class="trophies">${c.titles.map(y => `<span class="badge gold">🏆 ${esc(y)} champ</span>`).join('')}${c.runners.map(y => `<span class="badge">🥈 ${esc(y)}</span>`).join('')}${k === ME ? '<span class="badge gold">That\'s you</span>' : `<button class="badge" style="cursor:pointer;background:none" onclick="RD.setMe('${esc(k)}')">This is me</button>`}</div></div></div>
    <div class="stat-row" style="--n:4"><div><div class="sv">${c.w}-${c.l}</div><div class="sl">Record</div></div><div><div class="sv">${f(c.wp * 100)}%</div><div class="sl">Win rate</div></div><div><div class="sv">${c.titles.length}</div><div class="sl">Titles</div></div><div><div class="sv">${c.apps}</div><div class="sl">Playoff trips</div></div></div></section><div class="gap"></div>`;
  const tabs = [['overview', 'Overview'], ['games', 'Games'], ['rivals', 'Rivals'], ['players', 'Players'], ['moves', 'Trades']];
  h += `<div class="seg-row rise">${seg('team-tab', tabs, tab, 'RD.teamTab')}</div>`;
  const mine = FACTS.filter(x => x.keys.includes(k));
  if (tab === 'overview') {
    h += loreCard('lore-team', mine, { title: `${t.name} lore` }) + (mine.length ? '<div class="gap"></div>' : '');
    const res = c.res, his = res.slice().sort((a, b) => b.me - a.me);
    h += card('Career numbers', tiles([
      ['📈 Points per week', f2(c.ppg), `${f(c.pf)} total`], ['🎯 Head-to-head', `${c.hw}-${c.hl}`, `Playoffs: ${c.poW}-${c.poL}`],
      ['🌐 All-play', c.apn ? `${c.ap}-${c.apn - c.ap}` : '–', c.apn ? f(c.ap / c.apn * 100) + '% vs everyone' : ''], ['📊 Avg finish', c.avgRank ? ord(Math.round(c.avgRank)) : '–', 'Regular season'],
      ['💥 Best week', his[0] ? f2(his[0].me) : '–', his[0] ? M.gameLabel(his[0].g) : '', his[0] ? `RD.openGame(${his[0].g.id})` : ''], ['🧯 Worst week', his.length ? f2(his[his.length - 1].me) : '–', his.length ? M.gameLabel(his[his.length - 1].g) : '', his.length ? `RD.openGame(${his[his.length - 1].g.id})` : ''],
      ['🔥 Longest win run', c.ws, 'Median games included'], ['🧊 Longest skid', c.ls, 'Median games included'],
      ['👑 Weekly high scores', c.hiW, 'Times as the week\'s top scorer'], ['🪫 Weekly low scores', c.loW, 'Times as the week\'s lowest']]));
    h += '<div class="gap"></div>';
    h += card('Season by season', table(['Season', '', 'Finish', 'W-L', 'PF', 'PA', 'Eff.', 'Luck'], c.seasons.slice().reverse().map(x => [`<a class="link" href="#/standings/${esc(x.y)}">${esc(x.y)}</a>`, x.champ ? '🏆' : x.runner ? '🥈' : '', x.live ? `${ord(x.rank)} <span class="dim">(now)</span>` : x.place ? `${ord(x.place)}` : `${ord(x.rank)} <span class="dim">reg.</span>`, x.r ? `${x.r.w}-${x.r.l}` : '–', x.r ? f(x.r.pf) : '–', x.r ? f(x.r.pa) : '–', x.r ? f(x.r.eff) + '%' : '–', x.r ? `<span class="${cls(x.r.luck)}">${sg(x.r.luck)}</span>` : '–']), { stick: false }), { note: 'Finish is the final playoff placing where there is one, otherwise the regular-season spot.' });
    // weekly finish histogram
    if (c.ranks.length) {
      const n = M.TEAMS.length, cnt = Array.from({ length: n }, (_, i) => c.ranks.filter(r => r === i + 1).length), mx = Math.max(...cnt, 1);
      h += '<div class="gap"></div>' + card('Weekly finishes', `<div style="display:grid;grid-template-columns:repeat(${n},1fr);gap:5px;align-items:end;height:120px">${cnt.map((v, i) => `<div style="display:grid;gap:4px;align-items:end;height:100%"><div style="align-self:end;height:${Math.max(4, v / mx * 92)}px;border-radius:6px 6px 2px 2px;background:${i < n / 2 ? 'linear-gradient(var(--gold),var(--gold-dim))' : 'rgba(255,255,255,.16)'}" title="${v} weeks"></div></div>`).join('')}</div><div style="display:grid;grid-template-columns:repeat(${n},1fr);gap:5px;margin-top:6px;text-align:center;font-size:.66rem" class="dim">${cnt.map((v, i) => `<div><b style="color:var(--text)">${v}</b><br>${ord(i + 1)}</div>`).join('')}</div>`, { note: `Where ${nm(k)} ranked among all scores each regular-season week. Gold = top half.` });
    }
  } else if (tab === 'games') {
    const res = c.res.slice();
    const g5 = (list) => list.slice(0, 5).map(x => gameLine(x.g, k)).join('') || '<div class="empty">None yet.</div>';
    h += `<div class="two">${card('Best scores', g5(res.slice().sort((a, b) => b.me - a.me)))}${card('Worst scores', g5(res.slice().sort((a, b) => a.me - b.me)))}</div><div class="gap"></div>`;
    h += `<div class="two">${card('Biggest wins', g5(res.filter(x => x.me > x.os).sort((a, b) => (b.me - b.os) - (a.me - a.os))))}${card('Worst losses', g5(res.filter(x => x.me < x.os).sort((a, b) => (a.me - a.os) - (b.me - b.os))))}</div><div class="gap"></div>`;
    h += `<div class="two">${card('Nail-biter wins', g5(res.filter(x => x.me > x.os).sort((a, b) => (a.me - a.os) - (b.me - b.os))))}${card('Heartbreak losses', g5(res.filter(x => x.me < x.os).sort((a, b) => (b.me - b.os) - (a.me - a.os))))}</div><div class="gap"></div>`;
    const po = res.filter(x => x.g.type !== 'reg').sort((a, b) => b.g.y - a.g.y || b.g.w - a.g.w);
    h += card('Playoff games', po.map(x => gameLine(x.g, k)).join('') || '<div class="empty">No playoff games yet.</div>');
  } else if (tab === 'rivals') {
    const opp = Object.keys(M.TM).filter(o => o !== k && M.HH[k] && M.HH[k][o]).map(o => { const r = M.HH[k][o], n = r.w + r.l + r.t; return { o, r, n, wp: n ? (r.w + r.t / 2) / n : 0, mg: n ? (r.pf - r.pa) / n : 0, last: r.g.slice().sort((a, b) => b.y - a.y || b.w - a.w)[0] }; }).sort((a, b) => b.wp - a.wp || b.n - a.n);
    const q = opp.filter(x => x.n >= 2);
    const fav = q[0], nem = q[q.length - 1];
    if (fav && nem && fav !== nem) h += `<div class="two">${card('Favorite opponent', `<div class="tm" style="margin-top:6px">${av(fav.o, 'lg')}<div class="tm-t"><span class="tm-n" style="font-size:1.05rem">${nm(fav.o)}</span><span class="sb gold" style="font-size:1.6rem">${fav.r.w}-${fav.r.l}</span></div></div>`)}${card('Nemesis', `<div class="tm" style="margin-top:6px">${av(nem.o, 'lg')}<div class="tm-t"><span class="tm-n" style="font-size:1.05rem">${nm(nem.o)}</span><span class="sb loss" style="font-size:1.6rem">${nem.r.w}-${nem.r.l}</span></div></div>`)}</div><div class="gap"></div>`;
    h += card('Record against everyone', `<div class="rows">${opp.map(x => `<a class="row tap" href="#/h2h/${encodeURIComponent(k)}/${encodeURIComponent(x.o)}" style="grid-template-columns:minmax(0,1fr) auto"><span style="min-width:0;display:grid;gap:3px">${tm(x.o, { sub: false, size: 'sm', link: false })}<span class="dim" style="font-size:.7rem">Last: ${x.last ? `${esc(M.gameLabel(x.last))}, ${x.last.win === k ? 'won' : x.last.tie ? 'tied' : 'lost'} by ${f2(x.last.m)}` : '–'}</span></span><span class="rv"><span class="v ${x.r.w > x.r.l ? 'win' : x.r.w < x.r.l ? 'loss' : ''}">${x.r.w}-${x.r.l}${x.r.t ? '-' + x.r.t : ''}</span><span class="s">${sg(x.mg)} per game</span></span></a>`).join('') || '<div class="empty">No games yet.</div>'}</div>`, { note: 'Head-to-head games including playoffs (median games and consolation games not counted). Tap one for the full history.' });
  } else if (tab === 'players') {
    if (!M.hasLineups) h += card('Players', '<div class="empty">Player stats show up after the next data update, once weekly lineups are saved.</div>');
    else {
      const pg = M.PG.filter(p => p.k === k);
      const tot = {}; pg.forEach(p => { const x = tot[p.pid] || (tot[p.pid] = { pid: p.pid, pts: 0, n: 0, hi: 0 }); x.pts += p.pts; x.n++; x.hi = Math.max(x.hi, p.pts); });
      const L = Object.values(tot).sort((a, b) => b.pts - a.pts);
      h += card('Most points as a starter', `<div class="rows">${L.slice(0, 15).map((x, i) => `<div class="row" style="grid-template-columns:24px minmax(0,1fr) auto"><span class="rk">${i + 1}</span><span style="min-width:0;display:flex;align-items:center;gap:8px">${posBadge(M.ppos(x.pid))}<span class="tm-n">${esc(M.pname(x.pid))}</span></span><span class="rv"><span class="v">${f(x.pts)}</span><span class="s">${plural(x.n, 'start')} · ${f(x.pts / x.n)}/start</span></span></div>`).join('')}</div>`);
      h += '<div class="gap"></div>' + card('Best single games', `<div class="rows">${pg.slice().sort((a, b) => b.pts - a.pts).slice(0, 10).map((x, i) => `<div class="row tap" onclick="RD.openGame(${x.g.id})" style="grid-template-columns:24px minmax(0,1fr) auto"><span class="rk">${i + 1}</span><span style="min-width:0;display:grid;gap:3px"><span style="display:flex;align-items:center;gap:8px;min-width:0">${posBadge(M.ppos(x.pid))}<span class="tm-n">${esc(M.pname(x.pid))}</span></span><span class="dim" style="font-size:.7rem">${esc(M.gameLabel(x.g))}</span></span><span class="rv"><span class="v gold">${f2(x.pts)}</span></span></div>`).join('')}</div>`);
    }
  } else if (tab === 'moves') {
    const mt = M.TRD.filter(x => x.keys.includes(k));
    h += card(`Trades (${mt.length})`, mt.length ? mt.map(x => tradeCard(x, k)).join('') : '<div class="empty">No trades yet.</div>', { right: mt.length ? `<a class="r" href="#/trades/${encodeURIComponent(k)}">All trades ›</a>` : '' });
    h += '<div class="gap"></div>';
    const picks = M.allDrafts.filter(d => d.status === 'complete').flatMap(d => d.picks.filter(p => d.s.map[p.rid] === k).map(p => ({ ...p, d }))).sort((a, b) => b.d.season - a.d.season || a.n - b.n);
    const bySeason = [...new Set(picks.map(p => p.d.season))];
    h += card('Draft picks', bySeason.length ? bySeason.map(y => `<div class="eyebrow" style="margin:${y === bySeason[0] ? 0 : 14}px 0 6px">${y} draft · <a class="link" href="#/draft/${y}">board ›</a></div><div class="rows">${picks.filter(p => p.d.season === y).map(p => `<div class="row" style="grid-template-columns:50px minmax(0,1fr) auto;min-height:44px"><span class="dim tn" style="font-size:.78rem">${p.r}.${String(p.n - (p.r - 1) * (p.d.teams || M.TEAMS.length)).padStart(2, '0')}</span><span style="display:flex;align-items:center;gap:8px;min-width:0">${posBadge(p.pos)}<span class="tm-n">${esc(p.name || M.pname(p.pid))}</span></span><span class="dim" style="font-size:.72rem">#${p.n}</span></div>`).join('')}</div>`).join('') : '<div class="empty">No completed drafts.</div>');
  }
  return h;
};

/* ---------- HEAD TO HEAD ---------- */
P.h2h = function (args) {
  const keys = Object.keys(M.TM);
  let a = decodeURIComponent(args[0] || ''), b = decodeURIComponent(args[1] || '');
  if (!M.TM[a]) a = (ME && M.TM[ME]) ? ME : M.TEAMS[0].key;
  if (!M.TM[b] || b === a) { const r = Object.entries(M.HH[a] || {}).sort((x, y) => (y[1].w + y[1].l) - (x[1].w + x[1].l))[0]; b = r ? r[0] : M.TEAMS.find(t => t.key !== a).key; }
  const r = M.hh(a, b), n = r.w + r.l + r.t, games = r.g.slice().sort((x, y) => y.y - x.y || y.w - x.w);
  let h = pageHead('Head to head', 'Rivalry');
  h += `<div class="picker rise">${teamSelect('h2h-a', a, `RD.go('h2h/'+encodeURIComponent(this.value)+'/${encodeURIComponent(b)}')`, keys)}${teamSelect('h2h-b', b, `RD.go('h2h/${encodeURIComponent(a)}/'+encodeURIComponent(this.value))`, keys)}</div>`;
  const lead = r.w > r.l ? a : r.l > r.w ? b : null;
  h += `<section class="glass rise"><div class="vs"><a class="vs-side" href="#/team/${encodeURIComponent(a)}">${av(a, 'xl')}<span class="tm-n">${nm(a)}</span></a><div class="vs-mid"><div class="vs-score"><span class="${lead === a ? 'gold' : ''}">${r.w}</span><span class="d">–</span><span class="${lead === b ? 'gold' : ''}">${r.l}</span></div>${r.t ? `<span class="badge">${plural(r.t, 'tie')}</span>` : ''}<button class="vs-swap" type="button" aria-label="Swap sides" onclick="RD.go('h2h/${encodeURIComponent(b)}/${encodeURIComponent(a)}')">⇄</button></div><a class="vs-side" href="#/team/${encodeURIComponent(b)}">${av(b, 'xl')}<span class="tm-n">${nm(b)}</span></a></div>
    <div style="padding:0 16px 14px;text-align:center" class="dim">${n ? (lead ? `${nm(lead)} lead${''} the series` : 'The series is all square') : 'These two have never played.'}</div></section><div class="gap"></div>`;
  if (n) {
    const side = k => { const gs = games.map(g => ({ g, me: g.a === k ? g.sa : g.sb, op: g.a === k ? g.sb : g.sa })); return { gs, avg: mean(gs.map(x => x.me)), hi: Math.max(...gs.map(x => x.me)), big: Math.max(0, ...gs.map(x => x.me - x.op)), reg: gs.filter(x => x.g.type === 'reg'), po: gs.filter(x => x.g.type !== 'reg') }; };
    const A = side(a), B = side(b);
    const rec = (L) => `${L.filter(x => x.me > x.op).length}-${L.filter(x => x.me < x.op).length}`;
    const cs = (() => { let n = 0, w = null; for (const g of games) { const x = g.tie ? 'T' : g.win; if (w == null) w = x; if (x === w) n++; else break; } return { w, n }; })();
    const row = (k, va, vb, hiA) => `<div class="cmp"><span class="a ${hiA === true ? 'hi' : ''}">${va}</span><span class="k">${k}</span><span class="b ${hiA === false ? 'hi' : ''}">${vb}</span></div>`;
    h += card('Tale of the tape', row('Regular season', rec(A.reg), rec(B.reg)) + row('Playoffs', A.po.length ? rec(A.po) : '–', B.po.length ? rec(B.po) : '–') + row('Avg score', f2(A.avg), f2(B.avg), A.avg > B.avg ? true : A.avg < B.avg ? false : null) + row('Total points', f(r.pf), f(r.pa), r.pf > r.pa ? true : r.pf < r.pa ? false : null) + row('Best score', f2(A.hi), f2(B.hi), A.hi > B.hi ? true : A.hi < B.hi ? false : null) + row('Biggest win', A.big ? f2(A.big) : '–', B.big ? f2(B.big) : '–', A.big > B.big ? true : A.big < B.big ? false : null) + row('Streak', cs.w === a ? `W${cs.n}` : '', cs.w === b ? `W${cs.n}` : '', cs.w === a ? true : cs.w === b ? false : null));
    h += '<div class="gap"></div>' + card(`Every game (${n})`, games.map(g => gameLine(g, a)).join(''), { note: `From ${nm(a)}'s side. Tap a game to see both lineups.` });
  }
  // matrix
  const TK = M.TEAMS.map(t => t.key);
  const cell = (x, y) => { const q = M.HH[x] && M.HH[x][y]; if (!q || !(q.w + q.l + q.t)) return '<span class="faint">–</span>'; return `<a href="#/h2h/${encodeURIComponent(x)}/${encodeURIComponent(y)}" class="${q.w > q.l ? 'win' : q.w < q.l ? 'loss' : ''}" style="font-weight:700">${q.w}-${q.l}</a>`; };
  h += '<div class="gap"></div>' + card('Rivalry matrix', table(['', 'Team', ...TK.map(k => `<span title="${nm(k)}">${esc(T(k).code)}</span>`)], TK.map(x => [av(x, 'sm'), `<b>${nm(x)}</b>`, ...TK.map(y => x === y ? '<span class="faint">■</span>' : cell(x, y))]), { left: 2, rowCls: i => meCls(TK[i]) }), { note: `Row team's record against the column team. Tap a record to open it.<br>${TK.map(k => `<b>${esc(T(k).code)}</b> ${nm(k)}`).join(' · ')}` });
  return h;
};

/* ---------- GAME RECORDS ---------- */
const RECS = [
  { id: 'hi', t: 'Highest score', kind: 'side', v: x => x.x, dir: 1 },
  { id: 'lo', t: 'Lowest score', kind: 'side', v: x => x.x, dir: -1 },
  { id: 'blow', t: 'Biggest blowout', kind: 'game', v: g => g.m, dir: 1 },
  { id: 'close', t: 'Closest game', kind: 'game', v: g => g.m, dir: -1 },
  { id: 'tot', t: 'Most combined points', kind: 'game', v: g => g.tot, dir: 1 },
  { id: 'totlo', t: 'Fewest combined points', kind: 'game', v: g => g.tot, dir: -1 },
  { id: 'hiloss', t: 'Highest score in a loss', kind: 'game', v: g => g.ls, dir: 1, filt: g => !g.tie },
  { id: 'lowin', t: 'Lowest score in a win', kind: 'game', v: g => g.ws, dir: -1, filt: g => !g.tie },
  { id: 'po', t: 'Best playoff score', kind: 'side', v: x => x.x, dir: 1, filt: x => x.g.type !== 'reg' },
  { id: 'abmed', t: 'Furthest above the median', kind: 'side', v: x => x.x - x.g.W.md, dir: 1, filt: x => x.g.type === 'reg' && M.hasMed(x.g.s) },
  { id: 'player', t: 'Best player game', kind: 'player', v: p => p.pts, dir: 1 },
  { id: 'season', t: 'Best season (points per week)', kind: 'season', v: r => r.ppg, dir: 1 },
  { id: 'seasonlo', t: 'Worst season (points per week)', kind: 'season', v: r => r.ppg, dir: -1 }
];
function recList(rec, scope) {
  const inScope = g => scope === 'all' || String(g.y) === String(scope);
  let L = [];
  if (rec.kind === 'game') L = M.GH.filter(inScope).filter(rec.filt || (() => true)).map(g => ({ g, val: rec.v(g) }));
  if (rec.kind === 'side') L = M.GH.filter(inScope).flatMap(g => [{ k: g.a, x: g.sa, g }, { k: g.b, x: g.sb, g }]).filter(x => x.x > 0 || rec.dir > 0).filter(rec.filt || (() => true)).map(x => ({ ...x, val: rec.v(x) }));
  if (rec.kind === 'player') L = M.PG.filter(p => inScope(p.g)).map(p => ({ ...p, val: p.pts }));
  if (rec.kind === 'season') L = M.S.filter(s => scope === 'all' || String(s.season) === String(scope)).flatMap(s => M.SS[s.season].filter(r => r.wk >= 3).map(r => ({ r, s, k: r.key, val: rec.v(r) })));
  return L.sort((a, b) => rec.dir * (b.val - a.val));
}
function recLine(rec, x, i) {
  let main, sub, on = '';
  if (rec.kind === 'game') { main = rec.id === 'hiloss' ? `${nm(x.g.lose)} <span class="dim">lost to</span> ${nm(x.g.win)}` : `${nm(x.g.win)} <span class="dim">over</span> ${nm(x.g.lose)}`; sub = `${esc(M.gameLabel(x.g))} · ${f2(x.g.ws)}–${f2(x.g.ls)}`; on = `RD.openGame(${x.g.id})`; }
  if (rec.kind === 'side') { const o = x.g.a === x.k ? x.g.b : x.g.a; main = nm(x.k); sub = `${esc(M.gameLabel(x.g))} · ${x.g.win === x.k ? 'beat' : x.g.tie ? 'tied' : 'lost to'} ${nm(o)}`; on = `RD.openGame(${x.g.id})`; }
  if (rec.kind === 'player') { main = `${posBadge(M.ppos(x.pid))} ${esc(M.pname(x.pid))}`; sub = `${nm(x.k)} · ${esc(M.gameLabel(x.g))}`; on = `RD.openGame(${x.g.id})`; }
  if (rec.kind === 'season') { main = nm(x.k); sub = `${esc(x.s.season)} · ${x.r.w}-${x.r.l}${x.s === M.cur && M.inSeason ? ' (in progress)' : ''}`; on = `RD.go('team/${encodeURIComponent(x.k)}')`; }
  const k = x.k || (x.g && x.g.win);
  return `<div class="t10 tap${k === ME ? ' me-row' : ''}" onclick="RD.closeSheet();${on}"><span class="rk">${i + 1}</span><span style="min-width:0"><div class="tm-n">${main}</div><div class="d">${sub}</div></span><span class="v">${rec.id === 'abmed' ? '+' : ''}${f2(x.val)}</span></div>`;
}
P.records = function (args) {
  const scope = args[0] && M.S.some(s => String(s.season) === args[0]) ? args[0] : 'all';
  let h = pageHead('Game records', scope === 'all' ? 'All-time records' : `${esc(scope)} records`, 'Tap a record for its top 10');
  h += `<div class="seg-row rise">${seg('rec-scope', [['all', 'All-time'], ...M.S.slice().reverse().map(s => [s.season, s.season])], scope, 'RD.recScope')}</div>`;
  const cards = RECS.map(rec => {
    const L = recList(rec, scope); if (!L.length) return '';
    const x = L[0];
    const who = rec.id === 'hiloss' ? `${nm(x.g.lose)} <span class="dim">lost to</span> ${nm(x.g.win)}` : rec.kind === 'game' ? `${nm(x.g.win)} <span class="dim">over</span> ${nm(x.g.lose)}` : rec.kind === 'player' ? `${esc(M.pname(x.pid))} <span class="dim">for</span> ${nm(x.k)}` : nm(x.k);
    const when = rec.kind === 'season' ? esc(x.s.season) : esc(M.gameLabel(x.g));
    return `<div class="rec tap" onclick="RD.recTop('${rec.id}','${esc(scope)}')"><div class="t"><span>${rec.t}</span><span class="chev"></span></div><div class="v">${rec.id === 'abmed' ? '+' : ''}${f2(x.val)}</div><div class="w">${who}</div><div class="dim" style="font-size:.72rem">${when}</div></div>`;
  }).join('');
  h += card('', `<div class="rec-grid">${cards}</div>`) + (M.hasLineups ? '' : '<p class="note" style="margin:12px 4px">Player records show up after the next data update, once weekly lineups are saved.</p>');
  h += '<p class="note" style="margin:12px 4px">Consolation-bracket games are left out. Median games are not separate games, so they don\'t count either.</p>';
  return h;
};

/* ---------- TRADES ---------- */
function pickLabel(p, tr, rid) {
  const yr = p[0], rd = p[1], orig = p[2], okey = tr.s.map[orig];
  let out = `${yr} round ${rd} pick <span class="dim">(${orig === rid ? 'own pick back' : nm(okey) + "'s"})</span>`;
  const d = M.allDrafts.find(x => x.season === yr && x.status === 'complete' && x.picks.length && (!x.rounds || x.rounds >= rd));
  if (!d) return out + ' <span class="dim">· not drafted yet</span>';
  let slot = d.order ? d.order[okey] : null;
  if (slot == null && d.slots) slot = Number(Object.keys(d.slots).find(k => String(d.slots[k]) === String(orig)));
  const pk = d.picks.find(x => x.r === rd && x.slot === slot);
  if (!pk) return out + ' <span class="dim">· not drafted yet</span>';
  const pir = pk.n - (rd - 1) * (d.teams || M.TEAMS.length);
  return out + ` → ${posBadge(pk.pos)} <b>${esc(pk.name || 'Unknown')}</b> <span class="dim">(${rd}.${String(pir).padStart(2, '0')})</span>`;
}
function tradeCard(x, persp) {
  return `<div class="item" style="padding:12px 14px;margin-top:8px"><div class="dim" style="font-size:.72rem;margin-bottom:8px">${tdate(x.ts)} · ${esc(x.s.season)} season${x.week ? ` · Week ${x.week}` : ''}</div><div class="two" style="gap:12px">${x.keys.map((k, i) => { const rid = x.rosters[i]; const items = [...Object.entries(x.adds).filter(([, r]) => r === rid).map(([pid]) => `${posBadge(M.ppos(pid))} ${esc(M.pname(pid))}`), ...x.picks.filter(p => p[3] === rid).map(p => `🎟️ ${pickLabel(p, x, rid)}`)]; return `<div style="min-width:0">${tm(k, { sub: false, size: 'sm' })}<div class="dim" style="font-size:.68rem;text-transform:uppercase;letter-spacing:.07em;margin:8px 0 4px">Receives</div><div style="display:grid;gap:5px;font-size:.84rem">${items.map(s => `<div>${s}</div>`).join('') || '<span class="dim">Nothing</span>'}</div></div>`; }).join('')}</div></div>`;
}
P.trades = function (args) {
  const { TRD, S, TEAMS } = M;
  const flt = args[0] && M.TM[decodeURIComponent(args[0])] ? decodeURIComponent(args[0]) : '';
  let h = pageHead('Trades', 'Trade center', `${plural(TRD.length, 'trade')} since ${esc(S[0].season)}`);
  const tcount = TEAMS.map(t => { const m = TRD.filter(x => x.keys.includes(t.key)); const by = {}; S.forEach(s => by[s.season] = m.filter(x => x.s === s).length);
    const c = fn => m.reduce((n, x) => n + Object.entries(x.adds).filter(([, rid]) => fn(x.s.map[rid] === t.key)).length, 0);
    return { t, n: m.length, by, pin: c(v => v), pout: c(v => !v), kin: m.reduce((n, x) => n + x.picks.filter(p => x.s.map[p[3]] === t.key).length, 0), kout: m.reduce((n, x) => n + x.picks.filter(p => x.s.map[p[3]] !== t.key && x.s.map[p[2]] === t.key).length, 0) }; }).sort((a, b) => b.n - a.n);
  const tp = {}; TRD.forEach(x => { const k = [...x.keys].sort().join('|'); tp[k] = (tp[k] || 0) + 1; });
  const topP = Object.entries(tp).sort((a, b) => b[1] - a[1])[0];
  const top = tops(tcount, x => x.n), km = tops(tcount, x => x.kin);
  h += card('', tiles([['🔁 Total trades', TRD.length, [...new Set(TRD.map(x => x.s.season))].join(' · ') || '–'], ['🤝 Most active', top.v ? andList(top.items.map(x => nm(x.t.key))) : '–', top.v ? plural(top.v, 'trade') + (top.items.length > 1 ? ' each' : '') : ''], ['💞 Top partners', topP ? topP[0].split('|').map(nm).join(' + ') : '–', topP ? plural(topP[1], 'trade') : ''], ['🎟️ Most picks acquired', km.v ? andList(km.items.map(x => nm(x.t.key))) : '–', km.v ? km.v + ' picks' : '']]));
  h += '<div class="gap"></div>' + card('By team', table(['', 'Team', 'Total', ...S.map(s => esc(s.season)), 'Players in', 'Players out', 'Picks in'], tcount.map(x => [av(x.t.key, 'sm'), `<a href="#/trades/${encodeURIComponent(x.t.key)}"><b>${nm(x.t.key)}</b></a>`, `<b class="gold">${x.n}</b>`, ...S.map(s => x.by[s.season] || '–'), x.pin || '–', x.pout || '–', x.kin || '–']), { left: 2, rowCls: i => meCls(tcount[i].t.key) }));
  const TK = TEAMS.map(t => t.key);
  h += '<div class="gap"></div>' + card('Who trades with whom', table(['', 'Team', ...TK.map(k => esc(T(k).code))], TK.map(a => [av(a, 'sm'), `<b>${nm(a)}</b>`, ...TK.map(b => { if (a === b) return '<span class="faint">■</span>'; const n = TRD.filter(x => x.keys.includes(a) && x.keys.includes(b)).length; return n ? `<b class="gold">${n}</b>` : '<span class="faint">–</span>'; })]), { left: 2 }), { note: TK.map(k => `<b>${esc(T(k).code)}</b> ${nm(k)}`).join(' · ') });
  const list = flt ? TRD.filter(x => x.keys.includes(flt)) : TRD;
  h += '<div class="gap"></div>' + card('Trade log', `<div class="picker" style="margin:6px 0 4px"><select class="sel" onchange="RD.go('trades/'+encodeURIComponent(this.value))"><option value="">Every team</option>${TEAMS.map(t => `<option value="${esc(t.key)}"${t.key === flt ? ' selected' : ''}>${nm(t.key)}</option>`).join('')}</select></div>` + (list.length ? list.map(x => tradeCard(x)).join('') : '<div class="empty">No trades yet.</div>'), { id: 'log' });
  return h;
};

/* ---------- DRAFT BOARD ---------- */
P.draft = function (args) {
  const ds = M.allDrafts.filter(d => d.status === 'complete' && d.picks.length).sort((a, b) => b.season - a.season);
  let h = pageHead('Draft board', 'Drafts');
  if (!ds.length) return h + card('', '<div class="empty">No completed drafts yet.</div>');
  const d = ds.find(x => String(x.season) === String(args[0])) || ds[0];
  const view = args[1] === 'team' ? 'team' : 'board';
  const hi = args[2] ? decodeURIComponent(args[2]) : '';
  const nT = d.teams || M.TEAMS.length, rounds = d.rounds || Math.max(...d.picks.map(p => p.r));
  // slot -> original owner key
  const slotKey = {};
  if (d.order) Object.entries(d.order).forEach(([uid, slot]) => slotKey[slot] = uid);
  else if (d.slots) Object.entries(d.slots).forEach(([slot, rid]) => slotKey[slot] = d.s.map[rid]);
  h = pageHead('Draft board', `${esc(d.season)} draft`, `${rounds} rounds · ${esc(d.type || '')} order${d.picks.length < nT * rounds ? ` · ${d.picks.length} picks` : ''}`);
  h += `<div class="seg-row rise">${seg('dr-yr', ds.map(x => [x.season, x.season]), d.season, 'RD.draftYear')}${seg('dr-view', [['board', 'Board'], ['team', 'By team']], view, 'RD.draftView')}</div>`;
  const pk = p => { const k = d.s.map[p.rid], own = slotKey[p.slot], traded = own && k !== own, pos = p.pos || M.ppos(p.pid); return `<div class="pick pos-${esc(pos)}${traded ? ' traded' : ''}${hi && k !== hi ? ' dim' : ''}"><div class="pn"><span>${p.r}.${String(p.n - (p.r - 1) * nT).padStart(2, '0')}</span>${posBadge(pos)}</div><div class="pl">${esc(p.name || M.pname(p.pid))}</div><div class="pt">${traded ? '↪ ' : ''}${nm(k)}</div></div>`; };
  if (view === 'board') {
    const slots = Array.from({ length: nT }, (_, i) => i + 1);
    let g = `<div class="board"><div class="board-grid" style="--cols:${nT}"><div></div>${slots.map(s => `<div class="board-h" title="${slotKey[s] ? nm(slotKey[s]) : ''}">${slotKey[s] ? nm(slotKey[s]) : 'Slot ' + s}</div>`).join('')}`;
    for (let r = 1; r <= rounds; r++) {
      g += `<div class="board-r">${r}</div>` + slots.map(s => { const p = d.picks.find(x => x.r === r && x.slot === s); return p ? pk(p) : '<div class="pick empty"></div>'; }).join('');
    }
    g += '</div></div>';
    h += card('', `<div class="picker" style="margin-bottom:12px"><select class="sel" onchange="RD.go('draft/${d.season}/board/'+encodeURIComponent(this.value))"><option value="">Highlight a team…</option>${M.TEAMS.map(t => `<option value="${esc(t.key)}"${t.key === hi ? ' selected' : ''}>${nm(t.key)}</option>`).join('')}</select></div>` + g + `<div class="legend">${['QB', 'RB', 'WR', 'TE', 'K', 'DEF'].map(p => `<span>${posBadge(p)}</span>`).join('')}<span>↪ pick made by a team that traded for it</span></div>`, { note: 'Columns are draft slots, rows are rounds. Scroll sideways to see every slot.' });
  } else {
    const byTeam = {};
    d.picks.forEach(p => { const k = d.s.map[p.rid]; (byTeam[k] || (byTeam[k] = [])).push(p); });
    const order = Object.keys(byTeam).sort((a, b) => Math.min(...byTeam[a].map(p => p.n)) - Math.min(...byTeam[b].map(p => p.n)));
    h += `<div class="team-grid" style="grid-template-columns:repeat(auto-fill,minmax(min(100%,300px),1fr))">${order.map(k => card(tm(k, { sub: false, size: 'sm' }), `<div style="display:grid;gap:6px">${byTeam[k].sort((a, b) => a.n - b.n).map(p => { const pos = p.pos || M.ppos(p.pid); return `<div class="row" style="grid-template-columns:44px minmax(0,1fr);min-height:42px;padding:7px 10px"><span class="dim tn" style="font-size:.76rem">${p.r}.${String(p.n - (p.r - 1) * nT).padStart(2, '0')}</span><span style="display:flex;align-items:center;gap:8px;min-width:0">${posBadge(pos)}<span class="tm-n">${esc(p.name || M.pname(p.pid))}</span></span></div>`; }).join('')}</div>`, { cls: meCls(k) })).join('')}</div>`;
    // position mix
    const POSL = ['QB', 'RB', 'WR', 'TE'];
    h += '<div class="gap"></div>' + card('Position mix', table(['', 'Team', ...POSL, 'Other'], order.map(k => { const L = byTeam[k].map(p => p.pos || M.ppos(p.pid)); return [av(k, 'sm'), `<b>${nm(k)}</b>`, ...POSL.map(p => L.filter(x => x === p).length || '–'), L.filter(x => !POSL.includes(x)).length || '–']; }), { left: 2 }));
  }
  return h;
};

/* ---------- AWARDS ---------- */
P.awards = function () {
  const { CS, S, SS, cur, weekly, hasMed, REC, runs } = M;
  const mx = (a, k, d = 1) => tops(a, x => x[k], d);
  const out = [];
  const add = (title, t, fmt, tap) => { if (t.items.length) out.push([title, andList(t.items.map(x => nm(x.key || x.k))), fmt(t.items[0]), tap ? tap(t.items[0]) : '']); };
  add('🔥 Top scorer', mx(CS, 'pf'), t => f(t.pf) + ' pts');
  add('🧱 Stingiest schedule', mx(CS, 'pa', -1), t => f(t.pa) + ' pts against');
  add('🎯 Lineup guru', mx(CS.filter(t => t.pp), 'eff'), t => f(t.eff) + '% of max');
  add('🪑 Bench disaster', mx(CS.map(t => ({ ...t, left: t.pp - t.pf })), 'left'), t => f(t.left) + ' pts left on the bench');
  add('🍀 Luckiest', mx(CS, 'luck'), t => sg(t.luck) + ' wins vs expected');
  add('💀 Unluckiest', mx(CS, 'luck', -1), t => sg(t.luck) + ' wins vs expected');
  add('📈 Best point diff', mx(CS, 'diff'), t => sg(t.diff));
  add('📉 Worst point diff', mx(CS, 'diff', -1), t => sg(t.diff));
  add('⚡ Power #1', mx(CS, 'pow'), t => f(t.pow, 2) + ' power score');
  add('🛡️ Toughest schedule', mx(CS, 'pag'), t => f(t.pag) + ' PA per week');
  add('⭐ Highest ceiling', mx(CS, 'pp'), t => f(t.pp) + ' max points');
  const prev = S[S.length - 2];
  if (prev) { const PS = SS[prev.season]; const dd = CS.map(t => { const p = PS.find(x => x.key === t.key); return p && p.wk ? { ...t, d: t.ppg - p.ppg } : null; }).filter(Boolean); if (dd.length) { add('🔼 Most improved', mx(dd, 'd'), t => sg(t.d) + ' per week vs last year'); add('🔽 Biggest drop-off', mx(dd, 'd', -1), t => sg(t.d) + ' per week vs last year'); } }
  const W = weekly(cur), V = Object.values(W.T).map(t => ({ ...t, key: t.k }));
  if (V.length) {
    add('👑 Most weekly high scores', mx(V, 'cr'), t => plural(t.cr, 'week') + ' on top');
    add('🎢 Most consistent', mx(V.filter(v => v.sc.length > 1), 'sd', -1), t => '±' + f(t.sd) + ' week to week');
    add('🎰 Boom or bust', mx(V, 'sd'), t => '±' + f(t.sd) + ' week to week');
    add('🌐 Best all-play', mx(V.map(v => ({ ...v, apr: v.ap / (v.apn || 1) })), 'apr'), t => `${t.ap}-${t.apn - t.ap} vs everyone`);
    if (hasMed(cur)) { add('😭 Most unlucky losses', mx(V, 'ul'), t => plural(t.ul, 'loss', 'losses') + ' with an above-median score'); add('🤑 Most lucky wins', mx(V, 'lw'), t => plural(t.lw, 'win') + ' with a below-median score'); }
  }
  if (M.hasLineups) {
    const pg = M.PG.filter(p => p.g.s === cur);
    const t = tops(pg, p => p.pts); if (t.items.length) out.push(['🌟 Player game of the year', esc(M.pname(t.items[0].pid)), `${f2(t.v)} for ${nm(t.items[0].k)}, Week ${t.items[0].g.w}`, `RD.openGame(${t.items[0].g.id})`]);
  }
  let h = pageHead('Awards', `${esc(cur.season)} awards`, M.inSeason ? 'Season so far' : 'Final');
  h += card('', tiles(out));
  return h;
};

/* ---------- HISTORY ---------- */
P.history = function () {
  const { S, SS, cur, finished, done, CAR, TEAMS } = M;
  let h = pageHead('History', 'League history', `${esc(S[0].season)}–${esc(cur.season)}`);
  // titles count
  const champ = {}; finished.forEach(s => champ[s.champ] = (champ[s.champ] || 0) + 1);
  h += card('Champions', `<div class="rows">${finished.slice().reverse().map(s => `<a class="row is-lead" href="#/team/${encodeURIComponent(s.champ)}" style="grid-template-columns:58px minmax(0,1fr) auto"><span class="yr">${esc(s.season)}</span><span class="tm">${av(s.champ)}<span class="tm-t"><span class="tm-n">${nm(s.champ)}</span><span class="tm-u">${s.runner ? 'beat ' + nm(s.runner) + ' in the final' : esc(T(s.champ).user)}</span></span></span><span class="rv">🏆</span></a>`).join('') || '<div class="empty">No champions yet.</div>'}</div>`);
  h += '<div class="gap"></div>';
  // timeline
  h += `<div class="stack">${done.slice().reverse().map(s => {
    const std = SS[s.season];
    const pod = [s.champ, s.runner, s.third];
    const top = std[0], pts = std.slice().sort((a, b) => b.pf - a.pf)[0];
    return `<section class="glass card rise"><details class="disclose"><summary><span style="display:flex;align-items:baseline;gap:10px"><span class="yr">${esc(s.season)}</span><span class="dim" style="font-size:.8rem">${s.champ ? '🏆 ' + nm(s.champ) : 'Season'}</span></span></summary>
      ${s.champ ? `<div class="podium">${[1, 0, 2].map(i => pod[i] ? `<a class="pod p${i + 1}" href="#/team/${encodeURIComponent(pod[i])}"><span class="pl">${['Champion', 'Runner-up', 'Third'][i]}</span>${av(pod[i], i === 0 ? 'lg' : '')}<span class="tm-n">${nm(pod[i])}</span></a>` : '<div></div>').join('')}</div>` : ''}
      <div class="tiles mt">${[['Regular-season champ', nm(top.key), `${top.w}-${top.l}`], ['Points leader', nm(pts.key), f(pts.pf) + ' pts']].map(x => `<div class="tile"><div class="t">${x[0]}</div><div class="n">${x[1]}</div><div class="v">${x[2]}</div></div>`).join('')}</div>
      <div class="mt">${table(['#', 'Team', 'W-L', 'PF', 'PA', 'Finish'], std.map((t, i) => [i + 1, tm(t.key, { sub: false, size: 'sm' }), `${t.w}-${t.l}`, f(t.pf), f(t.pa), s.champ === t.key ? '<span class="gold">🏆 Champ</span>' : s.place[t.key] ? ord(s.place[t.key]) : s.inPO.has(t.key) ? 'Playoffs' : '<span class="dim">Missed</span>']), { cut: (s.settings.playoff_teams || 6) - 1, rowCls: i => meCls(std[i].key) })}</div></details></section>`;
  }).join('')}</div><div class="gap"></div>`;
  // all-time
  const AT = Object.values(CAR).filter(c => c.w + c.l).sort((a, b) => b.wp - a.wp);
  h += card('All-time standings', table(['#', 'Team', 'W-L', 'Win %', 'PF', 'PF/Wk', 'Playoffs', 'Titles'], AT.map((c, i) => [i + 1, tm(c.t.key, { sub: false, size: 'sm' }), `${c.w}-${c.l}`, f(c.wp * 100) + '%', f(c.pf), f(c.ppg), c.apps || '–', c.titles.length ? `<b class="gold">${c.titles.length}</b>` : '–']), { rowCls: i => meCls(AT[i].t.key) }), { note: `Every season${M.inSeason ? ', this one through the latest finished week' : ''}. Records include median games.` });
  // dynasty grid: finish per manager per season
  const yrs = S.map(s => s.season);
  const cellF = (k, s) => { const x = CAR[k].seasons.find(z => z.y === s.season); if (!x) return '<span class="faint">·</span>'; if (x.live) return `<span class="dim">${ord(x.rank)}*</span>`; if (x.champ) return '<b class="gold">🏆</b>'; const v = x.place || x.rank; return x.po ? `<b>${ord(v)}</b>` : `<span class="dim">${ord(v)}</span>`; };
  const ks = Object.keys(CAR).filter(k => CAR[k].seasons.length).sort((a, b) => (CAR[b].titles.length - CAR[a].titles.length) || CAR[a].avgRank - CAR[b].avgRank);
  h += '<div class="gap"></div>' + card('Dynasty grid', table(['', 'Team', ...yrs.map(esc)], ks.map(k => [av(k, 'sm'), `<a href="#/team/${encodeURIComponent(k)}"><b>${nm(k)}</b></a>`, ...S.map(s => cellF(k, s))]), { left: 2, rowCls: i => meCls(ks[i]) }), { note: 'Each season\'s final finish. Bold = made the playoffs, 🏆 = champion, * = season in progress.' });
  h += '<div class="gap"></div>' + card('League settings', `<div class="tiles">${[['Teams', M.TEAMS.length, ''], ['Playoff teams', cur.settings.playoff_teams || 6, `Starting Week ${M.ps(cur)}`], ['Median game', M.hasMed(cur) ? 'Yes' : 'No', M.hasMed(cur) ? 'Everyone also plays the median' : ''], ['Trade deadline', cur.settings.trade_deadline ? 'Week ' + cur.settings.trade_deadline : 'None', ''], ['Starting lineup', (cur.settings.roster_positions || []).length ? (cur.settings.roster_positions || []).map(p => p.replace('SUPER_FLEX', 'SF')).join(' · ') : '–', '']].map(x => `<div class="tile"><div class="t">${x[0]}</div><div class="n">${esc(x[1])}</div><div class="v">${esc(x[2])}</div></div>`).join('')}</div>`);
  return h;
};

/* =====================================================================
   Navigation, routing, chrome
   ===================================================================== */
const PAGES = [
  ['home', 'Home', '🏠'], ['standings', 'Standings', '📊'], ['teams', 'Managers', '👤'], ['h2h', 'Head to Head', '⚔️'],
  ['records', 'Game Records', '🏅'], ['power', 'Power & Luck', '⚡'], ['weekly', 'Weekly', '📅'], ['trades', 'Trades', '🔁'],
  ['draft', 'Draft Board', '📋'], ['awards', 'Awards', '🏆'], ['history', 'History', '📜']
];
const pageOf = r => r === 'team' ? 'teams' : r;
function renderNav(active) {
  const mount = $('#site-nav');
  const ln = M ? M.leagueName : 'Retirement Dynasty';
  const label = (PAGES.find(p => p[0] === pageOf(active)) || PAGES[0])[1];
  const ini = ln.split(/\s+/).map(w => w[0] || '').join('').slice(0, 2).toUpperCase();
  mount.innerHTML = `<div class="nav-bar"><button class="nav-toggle" id="nav-toggle" type="button" aria-label="Open menu" aria-expanded="false" aria-controls="drawer"><span class="bars"><span></span><span></span><span></span></span></button>
    <a class="brand" href="#/"><span class="brand-logo">${esc(ini)}</span><span class="brand-text"><span class="brand-league">${esc(ln)}</span><div class="brand-page">${esc(label)}</div></span></a>
    <nav class="nav-inline" aria-label="Pages">${PAGES.map(p => `<a href="#/${p[0] === 'home' ? '' : p[0]}" class="${p[0] === pageOf(active) ? 'active' : ''}"${p[0] === pageOf(active) ? ' aria-current="page"' : ''}>${p[1]}</a>`).join('')}</nav>
    <button class="me-btn" type="button" onclick="RD.pickMe()" aria-label="Choose your team">${ME && M && M.TM[ME] ? `${av(ME, 'sm')}<span class="t">${nm(ME)}</span>` : '<span class="av sm" style="--h:40">?</span><span class="t">This is me</span>'}</button></div>
    <div class="backdrop" id="backdrop"></div>
    <nav class="drawer" id="drawer" aria-hidden="true" aria-label="Pages"><div class="drawer-head"><span class="brand-logo">${esc(ini)}</span><div class="brand-page">${esc(ln)}</div></div>${PAGES.map(p => `<a href="#/${p[0] === 'home' ? '' : p[0]}" class="${p[0] === pageOf(active) ? 'active' : ''}"><span class="ic">${p[2]}</span>${p[1]}</a>`).join('')}${isInstalled() ? '' : `<button type="button" class="drawer-add" onclick="RD.installSheet()"><span class="ic">${ADD_SVG}</span>Add to Home Screen</button>`}<div class="drawer-foot">${M && D.generated ? `Updated ${esc(ago(D.generated))}` : ''}<br>Data from Sleeper</div></nav>`;
  $('#nav-toggle').onclick = () => $('#drawer').classList.contains('open') ? closeNav() : openNav();
  $('#backdrop').onclick = closeNav;
  $$('#drawer a').forEach(a => a.addEventListener('click', closeNav));
}
function openNav() { $('#drawer').classList.add('open'); $('#backdrop').classList.add('open'); $('#nav-toggle').classList.add('open'); $('#nav-toggle').setAttribute('aria-expanded', 'true'); $('#drawer').setAttribute('aria-hidden', 'false'); }
function closeNav() { const d = $('#drawer'); if (!d) return; d.classList.remove('open'); $('#backdrop').classList.remove('open'); $('#nav-toggle').classList.remove('open'); $('#nav-toggle').setAttribute('aria-expanded', 'false'); d.setAttribute('aria-hidden', 'true'); }
// Sticky bar that tucks away while scrolling down and comes back on the way up.
let lastY = 0;
window.addEventListener('scroll', () => {
  const y = window.scrollY, nav = $('#site-nav');
  if (!nav) return;
  if (y > lastY + 6 && y > 90) nav.classList.add('tuck');
  else if (y < lastY - 6 || y < 40) nav.classList.remove('tuck');
  lastY = y;
}, { passive: true });

let FACTS = [];
let lastRoute = null;
function parseHash() { const h = location.hash.replace(/^#\/?/, ''); const parts = h.split('/').filter(Boolean); return { r: parts[0] || 'home', args: parts.slice(1) }; }
function route(keepScroll) {
  if (!M) return;
  const { r, args } = parseHash();
  const fn = P[r] || P.home;
  const page = P[r] ? r : 'home';
  rememberSegs();
  const sameRoute = lastRoute && lastRoute.r === page;
  closeSheet();
  renderNav(page);
  let html;
  try { html = fn(args); } catch (e) { console.error(e); html = card('Something went wrong', `<div class="empty">This page hit an error: ${esc(e.message)}</div>`); }
  $('#app').innerHTML = html + footer();
  // stagger the rise-in, but only on a fresh page (not when flipping a selector)
  $$('#app .rise').forEach((el, i) => { if (sameRoute) el.classList.remove('rise'); else el.style.setProperty('--i', Math.min(i, 8)); });
  placeSegs();
  if (!sameRoute && !keepScroll) window.scrollTo(0, 0);
  $('#site-nav').classList.remove('tuck');
  document.title = page === 'home' ? M.leagueName : `${(PAGES.find(p => p[0] === pageOf(page)) || PAGES[0])[1]} · ${M.leagueName}`;
  lastRoute = { r: page, args };
}
function footer() {
  return `<footer class="site-foot">${esc(M.leagueName)} · ${M.S.map(s => esc(s.season)).join(', ')}<br>Data from Sleeper${D.generated ? ` · updated ${esc(ago(D.generated))}` : ''} · <a href="javascript:RD.refresh()">refresh</a></footer>`;
}
function go(path) { location.hash = '#/' + path; }
function replace(path) { history.replaceState(null, '', '#/' + path); route(true); }

/* ---------- "This is me" ---------- */
function setMe(k) {
  ME = k || null; LS.set('rd-me', ME);
  closeSheet(); route(true);
  toast(ME ? `Highlighting ${T(ME).name}` : 'Highlighting off');
}
function pickMe() {
  openSheet('Which team is yours?', 'Your team gets highlighted across the site, and Home shows your week.', `<div class="rows">${M.TEAMS.map(t => `<button class="row tap${t.key === ME ? ' is-lead' : ''}" type="button" style="grid-template-columns:minmax(0,1fr) auto;text-align:left;width:100%" onclick="RD.setMe('${esc(t.key)}')">${tm(t.key, { link: false })}<span class="rv">${t.key === ME ? '<span class="badge gold">You</span>' : ''}</span></button>`).join('')}${ME ? `<button class="row tap" type="button" style="grid-template-columns:1fr;width:100%;justify-items:center" onclick="RD.setMe('')"><span class="dim">Stop highlighting</span></button>` : ''}</div>`);
}

/* ---------- share ---------- */
async function share() {
  const url = location.href, title = document.title;
  try { if (navigator.share) { await navigator.share({ title, url }); return; } } catch (e) { if (e && e.name === 'AbortError') return; }
  try { await navigator.clipboard.writeText(url); toast('Link copied'); } catch (e) { prompt('Copy this link:', url); }
}

/* ---------- Add to Home Screen pop-up ----------
   iPhone/iPad: a sheet with the Share → Add to Home Screen steps (Safari has no
   install button a page can trigger). Android/desktop Chrome: a one-tap Install
   button. Shows a few seconds into a visit; "Not now" waits two weeks, "Don't
   show again" stops it for good, and the menu can always bring it back. */
const UA = navigator.userAgent;
const IOS = /iphone|ipad|ipod/i.test(UA) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
const IOS_OTHER = IOS && /CriOS|FxiOS|EdgiOS|OPiOS|GSA\//.test(UA);
const isInstalled = () => !!(window.navigator.standalone || matchMedia('(display-mode: standalone)').matches || LS.get('rd-installed'));
let installEvt = null;
window.addEventListener('beforeinstallprompt', e => { e.preventDefault(); installEvt = e; });
window.addEventListener('appinstalled', () => { LS.set('rd-installed', '1'); closeSheet(); toast('Added to your Home Screen'); });
const SHARE_SVG = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3v12M7.5 7.5 12 3l4.5 4.5M6 11H5a1 1 0 0 0-1 1v8a1 1 0 0 0 1 1h14a1 1 0 0 0 1-1v-8a1 1 0 0 0-1-1h-1"/></svg>';
const ADD_SVG = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><rect x="4" y="4" width="16" height="16" rx="4"/><path d="M12 8.5v7M8.5 12h7"/></svg>';
const DOTS_SVG = '<svg viewBox="0 0 24 24" fill="currentColor"><circle cx="6" cy="12" r="1.8"/><circle cx="12" cy="12" r="1.8"/><circle cx="18" cy="12" r="1.8"/></svg>';
function installSheet(fromMenu) {
  const head = `<div class="ins-hero"><img src="assets/icons/icon-192.png" alt="" width="64" height="64"><div><b>Retirement Dynasty</b><span>Opens full screen like an app, one tap from your Home Screen. Scores refresh on their own.</span></div></div>`;
  const foot = fromMenu ? '' : `<div class="ins-btns"><button type="button" class="ins-btn ghost" onclick="RD.installLater(false)">Don't show again</button><button type="button" class="ins-btn" onclick="RD.installLater(true)">Got it</button></div>`;
  let body;
  if (IOS) {
    const step = (n, ic, html) => `<li class="ins-step"><span class="ins-n">${n}</span><span class="ins-ic${n === 1 ? ' pulse-ic' : ''}">${ic}</span><span>${html}</span></li>`;
    body = head + `<ol class="ins-steps">
      ${step(1, SHARE_SVG, IOS_OTHER ? 'Tap the <b>Share</b> button in the address bar.' : 'Tap the <b>Share</b> button in Safari\'s toolbar. <span class="dim">Don\'t see it? Tap <span class="ins-inline">' + DOTS_SVG + '</span> first.</span>')}
      ${step(2, ADD_SVG, 'Scroll down and tap <b>Add to Home Screen</b>.')}
      ${step(3, '<b class="ins-add">Add</b>', 'Tap <b>Add</b> in the top corner. Done.')}
    </ol>` + foot;
  } else if (installEvt) {
    body = head + `<button type="button" class="ins-btn wide" onclick="RD.installNow()">Install the app</button>` + foot;
  } else {
    body = head + `<ol class="ins-steps"><li class="ins-step"><span class="ins-n">1</span><span class="ins-ic">${DOTS_SVG}</span><span>Open your browser's menu.</span></li><li class="ins-step"><span class="ins-n">2</span><span class="ins-ic">${ADD_SVG}</span><span>Choose <b>Add to Home screen</b> or <b>Install app</b>.</span></li></ol>` + foot;
  }
  openSheet('Add to Home Screen', '', body);
}
function a2hs() {
  if (isInstalled() || LS.get('rd-a2hs-never')) return;
  const snooze = Number(LS.get('rd-a2hs-later') || 0);
  if (Date.now() < snooze) return;
  const mobile = IOS || /android/i.test(UA);
  setTimeout(() => {
    if (document.hidden || $('#sheet') || $('#drawer.open') || isInstalled()) return;
    if (IOS || (mobile && installEvt)) installSheet(false);
  }, 4000);
}
/* ---------- data loading + refresh ---------- */
async function fetchData() {
  const r = await fetch('data/league.json?' + Date.now(), { cache: 'no-store' });
  if (!r.ok) throw new Error('HTTP ' + r.status);
  return r.json();
}
function ingest(data) {
  D = data; M = buildModel(D); FACTS = buildFacts();
  window.RD.M = M; window.RD.facts = FACTS;
}
async function refresh(silent) {
  try {
    const data = await fetchData();
    if (D && data.generated === D.generated) { if (!silent) toast('Already up to date'); return; }
    ingest(data); route(true);
    if (!silent) toast('Updated');
  } catch (e) { if (!silent) toast('Could not refresh'); }
}

window.RD = {
  go, share, openGame, closeSheet, setMe, pickMe, refresh,
  installSheet: () => { closeNav(); installSheet(true); },
  installLater(soon) { LS.set(soon ? 'rd-a2hs-later' : 'rd-a2hs-never', soon ? String(Date.now() + 14 * 864e5) : '1'); closeSheet(); if (!soon) toast('You can still find it in the menu'); },
  async installNow() { if (!installEvt) return; installEvt.prompt(); const r = await installEvt.userChoice.catch(() => null); installEvt = null; closeSheet(); if (r && r.outcome === 'accepted') LS.set('rd-installed', '1'); },
  homeWeek: w => replace('home/' + w),
  stdYear: y => replace('standings/' + y),
  weeklyYear: y => replace('weekly/' + y),
  teamTab: t => replace('team/' + encodeURIComponent(parseHash().args[0]) + '/' + t),
  recScope: s => replace('records/' + s),
  draftYear: y => replace('draft/' + y + '/' + (parseHash().args[1] || 'board')),
  draftView: v => replace('draft/' + (parseHash().args[0] || '') + '/' + v),
  recTop(id, scope) {
    const rec = RECS.find(r => r.id === id); if (!rec) return;
    const L = recList(rec, scope).slice(0, 10);
    openSheet(rec.t, scope === 'all' ? 'All-time top 10' : `${esc(scope)} top 10`, `<div class="top10">${L.map((x, i) => recLine(rec, x, i)).join('')}</div>`);
  }
};

window.addEventListener('hashchange', () => route());
window.addEventListener('resize', () => placeSegs());
(async function main() {
  renderNav('home');
  try { ingest(await fetchData()); }
  catch (e) {
    $('#app').innerHTML = card('No data yet', `<div class="empty">The league data file hasn't been created yet. In the GitHub repository, open <b>Actions</b>, choose <b>Update and deploy</b>, and press <b>Run workflow</b>. Come back in a minute.<br><span class="faint">(${esc(e.message)})</span></div>`);
    return;
  }
  route(true); a2hs();
  // Pick up new data (the updater runs every 10 minutes) while the page is open.
  setInterval(() => { if (!document.hidden) refresh(true); }, 3 * 60 * 1000);
  document.addEventListener('visibilitychange', () => { if (!document.hidden && D && Date.now() - new Date(D.generated) > 5 * 60 * 1000) refresh(true); });
  if ('serviceWorker' in navigator && location.protocol === 'https:') navigator.serviceWorker.register('sw.js').catch(() => {});
})();
})();
