// Copied from Dickory Linked Assurance isolation helper for THIS lab's scope.
self.addEventListener('install', e => e.waitUntil(self.skipWaiting()));
self.addEventListener('activate', e => e.waitUntil(self.clients.claim()));
self.addEventListener('fetch', event => {
  const request = event.request;
  if (new URL(request.url).origin !== self.location.origin) return;
  event.respondWith((async () => {
    const response = await fetch(request);
    if (response.status === 0) return response;
    const headers = new Headers(response.headers);
    headers.set('Cross-Origin-Opener-Policy', 'same-origin');
    headers.set('Cross-Origin-Embedder-Policy', 'require-corp');
    const body = request.method === 'HEAD' || [204,205,304].includes(response.status)
      ? null : response.body;
    return new Response(body, {status:response.status, statusText:response.statusText, headers});
  })());
});
