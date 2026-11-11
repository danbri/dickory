import {lessons} from '../tutorial-lessons.js';
import {spawnSync} from 'node:child_process';
import fs from 'node:fs/promises';
import {createHash} from 'node:crypto';
const root=new URL('../',import.meta.url),out=new URL('artifacts/tutorial/',root);
await fs.mkdir(out,{recursive:true});
const checks=[];
for(const lesson of lessons){
  for(const [kind,source,accepted] of [['example',lesson.source,lesson.expected!=='reject'],...(lesson.solution?[['repair',lesson.solution,true]]:[])]){
    const file=new URL(lesson.id+'.lean',out);await fs.writeFile(file,source);
    const result=spawnSync('lean',['--json',file.pathname],{encoding:'utf8',timeout:90000});
    if((result.status===0)!==accepted || accepted && /declaration uses [`']sorry[`']/.test(result.stdout))throw Error(lesson.id+': '+result.stdout+result.stderr);
    checks.push({lesson:lesson.id,kind,accepted});
  }
}
const report={status:'pass',compiler:spawnSync('lean',['--version'],{encoding:'utf8'}).stdout.trim(),
  sourceSha256:createHash('sha256').update(await fs.readFile(new URL('tutorial-lessons.js',root))).digest('hex'),checks};
await fs.writeFile(new URL('artifacts/tutorial-checks.json',root),JSON.stringify(report,null,2)+'\n');
console.log('Tutorial: '+checks.length+' native Lean checks passed, including deliberate rejection and repair.');
