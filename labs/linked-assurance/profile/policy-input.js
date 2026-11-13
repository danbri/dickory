// SPDX-License-Identifier: Apache-2.0
// ONE explicit state decoder for native Lean and browser Lean. No UI history.
import {decode} from './core.js';
import {policyInput} from './catalogue.js';
import {makeCase} from '../headless-contract.js';
import {fixtureSource,sha256} from '../evidence.js';
import {verifyCredential} from '../credential.js';
export async function preparePolicyInput(input,rdf,demo,source){
  const resolved=decode(policyInput,input),{identity,request}=makeCase(resolved),s=resolved.state;
  if(!/(Z|[+-]\d{2}:\d{2})$/.test(s.clock))throw Error('Clock needs an explicit timezone');
  const observedTime=Date.parse(s.clock);
  if(!Number.isSafeInteger(observedTime)||observedTime<0)throw Error('Invalid clock');
  const payload=s.credentialPayload??demo.payload,signature=s.credentialSignature??demo.signature;
  const verification=await verifyCredential(demo.publicKey,payload,signature);
  const operational={credentialVerified:verification.verified,observedTime,expiresAt:verification.expiresAt,
    secureTransportObserved:s.secureTransportObserved,permissionGranted:s.permissionGranted,
    attackerWantsInterruption:s.attackerWantsInterruption,legitimateSession:s.legitimateSession};
  const context=rdf.context||{datasetBytesSha256:await sha256(request.dataset),selectedGraphSha256:'unavailable',scope:JSON.stringify(request.scope),regime:request.regime,runtimeVersion:'0.35.1'};
  const fixture=fixtureSource(rdf,operational,context,request.queries);
  return {case:identity,resolved:{...resolved,state:{...s,credentialPayload:payload,credentialSignature:signature}},
    operational,verification,fixture,fixtureSha256:await sha256(fixture),sourceSha256:await sha256(source)};
}
