import {chromium} from 'playwright';
import fs from 'node:fs/promises';
const browser=await chromium.launch({headless:true});
try{
 const page=await browser.newPage();await page.goto('http://127.0.0.1:8081/labs/linked-assurance/');
 await page.exposeFunction('moduleProgress',s=>console.log(s));
 const result=await page.evaluate(async()=>{
  const {Lean4}=await import('./compiler.js');const lean=new Lean4({onProgress:window.moduleProgress});
  let ticks=0;const timer=setInterval(()=>ticks++,100);
  try{
   await lean.init();window.moduleProgress('Compiling Tiny.lean');
   const build=await lean.run('module\npublic import Init\n@[expose] public def answer : Nat := 42\npublic theorem fortyTwo : answer = 42 := by rfl',{moduleName:'Tiny',exportPrefix:'Tiny',flags:['--json','-o','/lib/lean/Tiny.olean']});
   if(build.exitCode!==0||!build.artifacts.includes('Tiny.olean'))throw Error(JSON.stringify(build));
   const runs=[];
   for(const [name,source,expected] of [
    ['import','public meta import Tiny\n#eval answer\n#check fortyTwo',0],
    ['reuse','public meta import Tiny\n#eval answer + 1',0],
    ['reject','public meta import Tiny\nexample : answer = 43 := by rfl',1],
    ['recover','public meta import Tiny\n#eval answer',0]]){
     window.moduleProgress(name);const start=performance.now();
     const r=await lean.run('module\npublic import Tiny\n'+source,{moduleName:'Run',persistent:true});
     if(r.exitCode!==expected)throw Error(name+': '+JSON.stringify(r));
     runs.push({name,milliseconds:Math.round(performance.now()-start),...r});
   }
   return {status:'pass',build,runs,uiHeartbeatTicks:ticks};
  }finally{clearInterval(timer);lean.dispose();}
 });
 await fs.writeFile('../../labs/linked-assurance/artifacts/module-browser-checks.json',JSON.stringify(result,null,2)+'\n');
 console.log(JSON.stringify(result));
}catch(error){
 await fs.writeFile('../../labs/linked-assurance/artifacts/module-browser-checks.json',JSON.stringify({status:'fail',error:String(error.stack||error)},null,2)+'\n');
 throw error;
}finally{await browser.close();}
