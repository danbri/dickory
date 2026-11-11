// Scoped to Linked Assurance Lab: isolate navigations and worker scripts.
// Does NOT proxy other origins or grant executable code extra capabilities.
self.addEventListener('install',e=>e.waitUntil(self.skipWaiting()));
self.addEventListener('activate',e=>e.waitUntil(self.clients.claim()));
self.addEventListener('fetch',event=>{
 const req=event.request;
 if(new URL(req.url).origin!==self.location.origin)return;
 event.respondWith((async()=>{
  const response=await fetch(req);
  const headers=new Headers(response.headers);
  headers.set('Cross-Origin-Opener-Policy','same-origin');
  headers.set('Cross-Origin-Embedder-Policy','credentialless');
  return new Response(response.body,{status:response.status,statusText:response.statusText,headers});
 })());
});
