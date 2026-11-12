// Scoped to Linked Assurance Lab: isolate navigations and worker scripts.
// Does NOT proxy other origins or grant executable code extra capabilities.
self.addEventListener('install',e=>e.waitUntil(self.skipWaiting()));
self.addEventListener('activate',e=>e.waitUntil(self.clients.claim()));
self.addEventListener('fetch',event=>{
 const req=event.request;
 if(new URL(req.url).origin!==self.location.origin)return;
 event.respondWith((async()=>{
  const response=await fetch(req);
  if(response.status===0)return response;
  const headers=new Headers(response.headers);
  headers.set('Cross-Origin-Opener-Policy','same-origin');
  // Safari does not implement credentialless. Our compiler assets are same-origin;
  // the Factoidal CDN is fetched with CORS, so require-corp works for both.
  headers.set('Cross-Origin-Embedder-Policy','require-corp');
  // WebKit can expose a stream even for a cached 304. Response construction
  // forbids bodies for these statuses (and a HEAD request has none either).
  const body=req.method==='HEAD'||[204,205,304].includes(response.status)?null:response.body;
  return new Response(body,{status:response.status,statusText:response.statusText,headers});
 })());
});
