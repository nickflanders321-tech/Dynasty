// Fetches your whole Sleeper league history and writes data/league.json.
// Runs on GitHub Actions (Node 20+). No packages needed.
import fs from 'node:fs/promises';

const API = 'https://api.sleeper.app/v1';
const OUT = 'data/league.json';
const NAMES = 'data/names.json';
const PLAYERS = 'data/players.json';
const DATA_VERSION = 2; // bump to rebuild finished seasons once when the saved shape changes
const FULL = process.env.FULL_REFRESH === 'true';
let calls = 0;

const sleep = ms => new Promise(r => setTimeout(r, ms));
const readJSON = async f => { try { return JSON.parse(await fs.readFile(f, 'utf8')); } catch { return null; } };
const r2 = x => Math.round((Number(x) || 0) * 100) / 100;

async function get(path, { optional = false } = {}) {
  let last;
  for (let i = 0; i < 4; i++) {
    try {
      calls++;
      const res = await fetch(API + path);
      if (res.status === 404 && optional) return null;
      if (!res.ok) throw new Error(`HTTP ${res.status} for ${path}`);
      const text = await res.text();
      return !text || text === 'null' ? null : JSON.parse(text);
    } catch (e) { last = e; await sleep(700 * (i + 1)); }
  }
  if (optional) { console.warn('Skipping (failed):', path, String(last)); return null; }
  throw last;
}

async function pool(items, n, fn) {
  const out = new Array(items.length);
  let i = 0;
  await Promise.all(Array.from({ length: Math.min(n, items.length) }, async () => {
    while (i < items.length) { const k = i++; out[k] = await fn(items[k], k); }
  }));
  return out;
}

function toGames(entries) {
  const groups = {};
  for (const m of entries || []) {
    if (m.matchup_id == null) continue;
    (groups[m.matchup_id] ||= []).push(m);
  }
  return Object.values(groups).filter(g => g.length === 2)
    .map(([a, b]) => [a.roster_id, r2(a.points), b.roster_id, r2(b.points)]);
}

const cfg = await readJSON('config.json');
if (!cfg?.league_id) throw new Error('config.json must contain {"league_id": "..."}');

const state = await get('/state/nfl');
const prev = await readJSON(OUT);
const prevById = {};
(prev?.seasons || []).forEach(s => { prevById[s.league_id] = s; });
const names = (await readJSON(NAMES)) || {};

// Walk back through every season of the league.
const leagues = [];
{
  const seen = new Set();
  let id = String(cfg.league_id);
  while (id && id !== '0' && !seen.has(id)) {
    seen.add(id);
    const L = await get(`/league/${id}`);
    leagues.push(L);
    id = L.previous_league_id ? String(L.previous_league_id) : null;
  }
}
console.log(`Found ${leagues.length} season(s):`, leagues.map(l => l.season).join(', '));

const draftNames = {};

async function buildSeason(L) {
  const old = prevById[L.league_id];
  if (!FULL && old && old.v === DATA_VERSION && old.status === 'complete' && L.status === 'complete') {
    console.log(`Reusing ${L.season} (complete)`);
    (old.drafts || []).forEach(d => d.picks.forEach(p => { if (p.pid && p.name) draftNames[p.pid] = [p.name, p.pos || '']; }));
    return old;
  }
  const id = L.league_id;
  const finished = L.status === 'complete' || Number(L.season) < Number(state.season);
  const maxWeek = finished ? 18 : Math.min(18, Math.max(Number(state.week) || 1, 1) + 1);
  const weeks = Array.from({ length: maxWeek }, (_, i) => i + 1);

  const [users, rosters] = await Promise.all([get(`/league/${id}/users`), get(`/league/${id}/rosters`)]);
  const mu = await pool(weeks, 6, w => get(`/league/${id}/matchups/${w}`, { optional: true }));
  const tx = await pool(weeks, 6, w => get(`/league/${id}/transactions/${w}`, { optional: true }));
  const bracket = await get(`/league/${id}/winners_bracket`, { optional: true });
  const draftList = (await get(`/league/${id}/drafts`, { optional: true })) || [];

  const byUser = {};
  (users || []).forEach(u => { byUser[u.user_id] = u; });
  const teams = (rosters || []).map(r => {
    const u = byUser[r.owner_id] || {};
    return { roster_id: r.roster_id, owner_id: r.owner_id || null, display_name: u.display_name || '', team_name: u.metadata?.team_name || '', avatar: u.metadata?.avatar || (u.avatar ? `https://sleepercdn.com/avatars/thumbs/${u.avatar}` : null) };
  });
  const standings = (rosters || []).map(r => {
    const s = r.settings || {};
    return {
      roster_id: r.roster_id, w: s.wins || 0, l: s.losses || 0, t: s.ties || 0,
      pf: r2((s.fpts || 0) + (s.fpts_decimal || 0) / 100),
      pa: r2((s.fpts_against || 0) + (s.fpts_against_decimal || 0) / 100),
      pp: r2((s.ppts || 0) + (s.ppts_decimal || 0) / 100),
      record: r.metadata?.record || '', streak: r.metadata?.streak || ''
    };
  });

  const weekRows = [];
  weeks.forEach((w, i) => {
    const games = toGames(mu[i]);
    if (!games.length) return;
    // Each team's starters that week as [player_id, points] (empty slots left out).
    const lu = {};
    for (const m of mu[i] || []) {
      if (m.matchup_id == null || !Array.isArray(m.starters)) continue;
      lu[m.roster_id] = m.starters.map((pid, k) => [String(pid), r2(m.starters_points?.[k])]).filter(([pid]) => pid && pid !== '0');
    }
    weekRows.push({ week: w, games, lu });
  });

  const trades = [];
  tx.forEach((arr, i) => (arr || []).forEach(t => {
    if (t.type !== 'trade' || t.status !== 'complete') return;
    trades.push({
      ts: t.created, week: t.leg ?? i + 1, rosters: t.roster_ids || [],
      adds: t.adds || {},
      picks: (t.draft_picks || []).map(p => [Number(p.season), p.round, p.roster_id, p.owner_id])
    });
  }));
  trades.sort((a, b) => a.ts - b.ts);

  const drafts = [];
  for (const d of draftList) {
    const oldD = (old?.drafts || []).find(x => x.draft_id === d.draft_id && x.status === 'complete');
    let entry = oldD;
    if (!entry || FULL) {
      const complete = d.status === 'complete';
      const picks = complete ? ((await get(`/draft/${d.draft_id}/picks`, { optional: true })) || []) : [];
      entry = {
        draft_id: d.draft_id, season: Number(d.season), status: d.status, type: d.type,
        rounds: d.settings?.rounds || null, teams: d.settings?.teams || null,
        order: d.draft_order || null, slots: d.slot_to_roster_id || null,
        picks: picks.map(p => ({
          r: p.round, n: p.pick_no, slot: p.draft_slot, rid: p.roster_id, pid: p.player_id,
          name: [p.metadata?.first_name, p.metadata?.last_name].filter(Boolean).join(' '),
          pos: p.metadata?.position || ''
        }))
      };
    }
    entry.picks.forEach(p => { if (p.pid && p.name) draftNames[p.pid] = [p.name, p.pos || '']; });
    drafts.push(entry);
  }

  const s = L.settings || {};
  return {
    v: DATA_VERSION, season: L.season, league_id: id, name: L.name, status: L.status, avatar: L.avatar || null,
    settings: {
      playoff_week_start: s.playoff_week_start || 15, playoff_teams: s.playoff_teams || 6,
      median: s.league_average_match === 1, trade_deadline: s.trade_deadline || null,
      teams: L.total_rosters || teams.length,
      roster_positions: (L.roster_positions || []).filter(p => !['BN', 'IR', 'TAXI'].includes(p))
    },
    teams, standings, weeks: weekRows, trades, bracket: bracket || [], drafts
  };
}

const built = [];
for (const L of leagues) built.push(await buildSeason(L));
built.sort((a, b) => Number(a.season) - Number(b.season));

// Resolve a name and position for every player the site shows: traded players,
// drafted players and every starter. Cached in data/players.json so the big
// Sleeper player list is only downloaded when someone new shows up.
const players = (await readJSON(PLAYERS)) || {};
Object.entries(names).forEach(([pid, n]) => { if (!players[pid] && n && !/^Player #/.test(n)) players[pid] = [n, '']; });
const wanted = new Set();
built.forEach(s => {
  s.trades.forEach(t => Object.keys(t.adds).forEach(p => wanted.add(p)));
  (s.drafts || []).forEach(d => d.picks.forEach(p => p.pid && wanted.add(String(p.pid))));
  s.weeks.forEach(w => Object.values(w.lu || {}).forEach(l => l.forEach(([pid]) => wanted.add(pid))));
});
wanted.forEach(pid => {
  const d = draftNames[pid];
  if (d && (!players[pid] || !players[pid][1])) players[pid] = [d[0], d[1] || (players[pid] && players[pid][1]) || ''];
});
const missing = [...wanted].filter(p => !players[p] || !players[p][1]);
if (missing.length) {
  console.log(`Looking up ${missing.length} player(s) in the full player list...`);
  const all = await get('/players/nfl', { optional: true });
  if (all) missing.forEach(pid => {
    const p = all[pid];
    const name = p && (p.full_name || [p.first_name, p.last_name].filter(Boolean).join(' '));
    // Team defenses have no name fields, just a team code.
    const nm = name || (p && p.position === 'DEF' && p.team ? `${p.team} Defense` : null) || (players[pid] && players[pid][0]) || (/^[A-Z]{2,3}$/.test(pid) ? `${pid} Defense` : `Player #${pid}`);
    // '?' marks a player the list doesn't know, so it isn't looked up again every run.
    players[pid] = [nm, (p && (p.position || p.fantasy_positions?.[0])) || (/^[A-Z]{2,3}$/.test(pid) ? 'DEF' : '?')];
  });
}
const outNames = {}, outPos = {};
wanted.forEach(pid => { const p = players[pid]; if (p) { outNames[pid] = p[0]; if (p[1] && p[1] !== '?') outPos[pid] = p[1]; } });
Object.keys(players).forEach(pid => { if (players[pid][0]) names[pid] = players[pid][0]; });

const body = {
  state: { season: state.season, week: state.week, season_type: state.season_type },
  seasons: built, names: outNames, pos: outPos
};
const strip = o => JSON.stringify({ ...o, generated: undefined });
const prevBody = prev ? strip(prev) : null;
await fs.mkdir('data', { recursive: true });
await fs.writeFile(NAMES, JSON.stringify(names));
await fs.writeFile(PLAYERS, JSON.stringify(players));
if (prevBody === strip(body)) {
  console.log(`No data changes (${calls} API calls).`);
} else {
  await fs.writeFile(OUT, JSON.stringify({ generated: new Date().toISOString(), ...body }));
  console.log(`Wrote ${OUT} (${calls} API calls).`);
}
