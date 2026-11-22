import {checkMobileLean,mobileLeanAvailable} from './inline-lean-host.js';
import {auditContract,diagnosticText} from '../linked-assurance/lean-host.js';
import {sha256Source} from './proof-evidence.js';

const REQUIRED=[
  'SWADAccounts.acid_ignores_stock',
  'SWADAccounts.archived_rule8_counterexample',
  'SWADAccounts.archived_rule10_counterexample',
  'SWADAccounts.archived_rule11_predicate_mismatch'
];
const FALSE_CLAIM=[
  '',
  'example : SWADAccounts.sameExactValue',
  '    (SWADAccounts.acidTest SWADAccounts.fixture)',
  '    (SWADAccounts.archivedN3AcidTest SWADAccounts.fixture) = true := by',
  '  decide',
  ''
].join('\n');

export function mountInlineCompiler({source,contract}){
  const $=id=>document.getElementById(id);
  const status=$('inlineCompilerStatus');
  const start=$('runInline');
  const negative=$('runInlineNegative');
  let running=false;

  function message(value){status.textContent=value;}
  async function positive(snapshot){
    const unavailable=mobileLeanAvailable();
    if(unavailable){
      message('Inline Lean unavailable: '+unavailable+' This is a setup limitation, not a theorem rejection.');
      return false;
    }
    message('Starting real on-device Lean 4.33.1 proof check…');
    let result;
    try {
      result=await checkMobileLean(snapshot+'\n'+contract,progress=>message(progress));
    } catch(error){
      message('Local Lean compiler failed: '+String(error.message||error).split('\n')[0]+
        '\nThe source is NOT verified on this device; see independent native CI evidence below.');
      return false;
    }
    if(snapshot!==source()){
      message('Source changed during compilation. This result is STALE and does not verify current editor bytes.');
      return false;
    }
    if(result.runtimeFault){
      message('LEAN WASM RUNTIME FAULT (not theorem rejection): '+result.diagnostics.slice(0,550));
      return false;
    }
    const valid=result.accepted&&REQUIRED.every(name=>auditContract(result,name));
    $('diagnostics').textContent=diagnosticText(result).slice(0,12000);
    const hash=await sha256Source(snapshot);
    if(!valid){
      message(result.accepted
        ? 'Lean accepted the file but the required theorem/axiom audit was incomplete. NO PROOF CERTIFIED.'
        : 'Lean returned a source error. The source is NOT verified locally; inspect real diagnostics below.');
      return false;
    }
    message('LOCAL LEAN 4.33.1 PROOF ACCEPTED by the on-device WASM compiler.\n'+
      'Actual source SHA-256: '+hash+'\n'+
      'Runtime: '+result.compilerVersion+'\n'+
      'Four required theorem type checks and permitted axiom reports passed.');
    return true;
  }
  async function guarded(fn){
    if(running)return;
    running=true;start.disabled=negative.disabled=true;
    try{await fn();}
    catch(e){message('Local Lean operation failed: '+String(e.message||e));}
    finally{running=false;start.disabled=negative.disabled=false;}
  }
  start.onclick=()=>guarded(()=>positive(source()));
  negative.onclick=()=>guarded(async()=>{
    const snapshot=source();
    if(!await positive(snapshot)){
      message(status.textContent+'\nNegative test not run because the current positive contract was not established.');
      return;
    }
    let result;
    try {
      result=await checkMobileLean(snapshot+'\n'+contract+FALSE_CLAIM,progress=>message(progress));
    } catch(error){
      message('Local runtime failure, NOT a rejection: '+String(error.message||error).split('\n')[0]);return;
    }
    if(snapshot!==source()){message('Editor changed while negative test ran: result is stale.');return;}
    if(result.runtimeFault){
      message('Local runtime fault, NOT a rejection: '+result.diagnostics.slice(0,550));return;
    }
    $('diagnostics').textContent=diagnosticText(result).slice(0,12000);
    const structured=String(result.stdout||'').split('\n').flatMap(line=>{
      try{const obj=JSON.parse(line);return obj.severity==='error'?[obj.data||'']:[];}catch{return[];}
    });
    if(result.exitCode!==0&&structured.length>0&&!result.accepted){
      message('LOCAL LEAN 4.33.1 NEGATIVE CHECK: expected false theorem REJECTED by the real compiler.\n'+
        'This is a Lean diagnostic, not a worker crash.');
    }else{
      message('NEGATIVE GATE FAILED: the compiler did not return an expected Lean error. Inspect diagnostics.');
    }
  });
  const unavailable=mobileLeanAvailable();
  message(unavailable?'Inline Lean requires setup: '+unavailable:
    'Ready for genuine on-device Lean 4.33.1. The binary downloads only when you press Verify.');
}
