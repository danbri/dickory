import {sha256} from './evidence.js';
export async function verifyCredential(trustAnchor,payload,signature) {
  try {
    const record=JSON.parse(payload);
    if(record.subject!=='urn:lab:principal')throw Error('Credential subject does not match the catalogue principal.');
    const expiresAt=Date.parse(record.expiresAt);
    if(!Number.isSafeInteger(expiresAt)||expiresAt<0)throw Error('Invalid expiry.');
    const key=await crypto.subtle.importKey('jwk',trustAnchor,{name:'ECDSA',namedCurve:'P-256'},false,['verify']);
    const bytes=Uint8Array.from(atob(signature),c=>c.charCodeAt(0));
    const verified=await crypto.subtle.verify({name:'ECDSA',hash:'SHA-256'},key,bytes,new TextEncoder().encode(payload));
    return {verified,expiresAt,payloadSha256:await sha256(payload),keySha256:await sha256(JSON.stringify(trustAnchor)),
      algorithm:'ECDSA P-256 / SHA-256',subject:record.subject,scope:'Demo credential payload only; not artifact, identity or consent verification.'};
  }catch(e){return {verified:false,expiresAt:0,error:String(e.message||e)};}
}
