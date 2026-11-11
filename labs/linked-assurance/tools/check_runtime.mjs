import {spawnSync} from 'node:child_process';
import fs from 'node:fs/promises';
import {createHash} from 'node:crypto';
const root=new URL('../',import.meta.url);
const test=spawnSync(process.execPath,['--test','tests/evidence.test.mjs'],{cwd:root,encoding:'utf8'});
process.stdout.write(test.stdout);process.stderr.write(test.stderr);
if(test.status!==0)process.exit(test.status||1);
const files=['app.js','evidence.js','pipeline-record.js','credential.js','rdf-worker.js','lean-host.js','compiler.js','compiler-worker.js','compiler-cache.js','compiler-banner.js','tutorial.js','tutorial-lessons.js','scenarios.js','demo-credential.json'];
const hashes={};for(const file of files)hashes[file]=createHash('sha256').update(await fs.readFile(new URL(file,root))).digest('hex');
await fs.mkdir(new URL('artifacts/',root),{recursive:true});
await fs.writeFile(new URL('artifacts/runtime-checks.json',root),JSON.stringify({status:'pass',runtime:'@factoidal/core 0.35.1',
  testFile:'tests/evidence.test.mjs',sha256:hashes,output:test.stdout},null,2)+'\n');
