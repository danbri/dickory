import {mountCompilerBanner} from '../../compiler-banner.js';
import {checkLean} from '../../lean-host.js';
import './checks.js';
const $=id=>document.getElementById(id);
mountCompilerBanner($('compilerBanner'));
$('run').onclick=async()=>{
  $('run').disabled=true;$('result').textContent='';const cases=[],started=performance.now();let phase='Starting…';
  const timer=setInterval(()=>$('status').textContent=phase+' · '+Math.round((performance.now()-started)/1000)+' s',1000);
  try{
    for(const [name,source,wanted,pattern] of globalThis.leanHello.cases){
      phase='Checking '+name;
      const result=await checkLean(source,text=>{phase=text;}),messages=result.stdout.split('\n').flatMap(line=>{try{return [JSON.parse(line)];}catch{return [];}});
      cases.push({name,...result});
      if(result.exitCode!==wanted || result.accepted!==(wanted===0) || pattern&&!messages.some(m=>pattern.test(m.data||'')))throw Error('Unexpected compiler result for '+name);
    }
    $('status').textContent='All checks passed, including rejection of the false theorem.';
  }catch(e){$('status').textContent=e.message;}
  finally{clearInterval(timer);$('result').textContent=JSON.stringify(cases,null,2);$('run').disabled=false;}
};
