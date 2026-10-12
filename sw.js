// Offline fallback for the Home Screen app. Always tries the network first, so
// the site is never stale while online; the cached copy is only used when
// there is no connection.
const CACHE = 'rd-v1';
const SHELL = ['./', 'index.html', 'assets/app.css', 'assets/app.js', 'assets/eggs.js', 'assets/icons/icon-192.png'];

self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(SHELL)).then(() => self.skipWaiting()));
});

self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET' || new URL(req.url).origin !== location.origin) return;
  // league.json is requested with a cache-busting query; store it under one key.
  const key = req.url.includes('data/league.json') ? new Request(new URL('data/league.json', self.registration.scope)) : req;
  e.respondWith(
    fetch(req).then(res => {
      if (res.ok) { const copy = res.clone(); caches.open(CACHE).then(c => c.put(key, copy)); }
      return res;
    }).catch(() => caches.match(key).then(r => r || caches.match('index.html')))
  );
});
