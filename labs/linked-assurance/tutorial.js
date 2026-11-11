import {lessons} from './tutorial-lessons.js';
import {checkLean,hasProofPlaceholder} from './lean-host.js';

export function mountTutorial(target){
  target.innerHTML=`<div class="tutorialIntro"><p class="eyebrow">A LITTLE LEAN</p><h1>One small proof<br>at a time.</h1><p>You know a little functional programming. Start there. Predict an answer, ask Lean, change something. ${lessons.length} short conversations lead from values to proofs, then to promises about programs and ways those promises can mislead.</p></div>
  <div class="tutorialLayout"><nav id="lessonNav" aria-label="Lean lessons"></nav>
  <article class="lesson"><p id="lessonNumber" class="eyebrow"></p><h2 id="lessonTitle"></h2><p id="lessonLead"></p>
    <div class="lessonQuestion"><b>Pause and predict</b><p id="lessonQuestion"></p>
    <details id="lessonAnswer"><summary>Think, then reveal</summary><p id="lessonAnswerText"></p></details></div>
    <label for="tutorialEditor">Your Lean file · editable · each lesson stands alone</label>
    <textarea id="tutorialEditor" spellcheck="false" autocapitalize="off" autocomplete="off"></textarea>
    <div class="actions"><button id="tutorialRun">Check with Lean</button><button id="tutorialReset" class="secondary">Restore this example</button><button id="tutorialDownload" class="secondary">Save .lean file</button></div>
    <p id="tutorialStatus" role="status">Ready. The first check loads Lean; later checks reuse it.</p>
    <pre id="tutorialOutput" aria-label="Lean output" hidden></pre>
    <details id="tutorialDiagnostics"><summary>Full compiler diagnostics</summary><pre id="tutorialRaw"></pre></details>
    <div class="lessonExperiment"><b>Try a small change</b><p id="lessonTry"></p></div><p id="lessonTakeaway"></p>
    <p class="hint">“Accepted” describes the file you submitted, not whether you completed an exercise. This is a small playground, not a live goal editor. Remove a tactic and check to inspect the unfinished goal. Ctrl/⌘ + Enter runs the file.</p>
    <div class="lessonPager"><button id="lessonPrevious" class="secondary">← Previous</button><span id="lessonPosition"></span><button id="lessonNext">Next →</button></div>
  </article></div>
  <footer>Continue with <a href="https://lean-lang.org/theorem_proving_in_lean4/">Theorem Proving in Lean 4</a> or <a href="#workbench">return to the policy workbench</a>. These examples use Lean’s core library, with no RDF library required.</footer>`;
  const $=id=>target.querySelector('#'+id),text=(id,s)=>{$(id).textContent=s;};
  let current=0,epoch=0,running=false,drafts={};
  try{drafts=JSON.parse(localStorage.getItem('linked-assurance-lean-lessons-v1')||'{}');if(!drafts||Array.isArray(drafts)||typeof drafts!=='object')drafts={};}catch{}
  const save=()=>{try{localStorage.setItem('linked-assurance-lean-lessons-v1',JSON.stringify(drafts));}catch{}};
  const nav=lessons.map((lesson,i)=>{const b=document.createElement('button');b.textContent=String(i+1).padStart(2,'0')+' / '+lesson.title;b.onclick=()=>{location.hash='learn/'+lesson.id;};return b;});
  $('lessonNav').replaceChildren(...nav);
  function display(){
    const id=location.hash.split('/')[1],found=lessons.findIndex(l=>l.id===id);current=found<0?0:found;epoch++;
    const l=lessons[current];
    text('lessonNumber',l.topic+' · '+(current+1)+' / '+lessons.length);text('lessonTitle',l.title);text('lessonLead',l.lead);text('lessonQuestion',l.question);text('lessonAnswerText',l.answer);text('lessonTry',l.tryIt);text('lessonTakeaway',l.takeaway);
    $('tutorialEditor').value=typeof drafts[l.id]==='string'?drafts[l.id]:l.source;
    $('lessonAnswer').open=false;$('tutorialDiagnostics').open=false;$('tutorialOutput').hidden=true;text('tutorialRaw','');
    text('tutorialStatus',running?'A Lean check is still running; wait before checking this file.':$('tutorialEditor').value!==l.source?'Your saved edit is ready to check.':l.expected==='reject'?'This example deliberately fails. Run it, read the error, then repair the claim.':'Ready to check.');
    text('lessonPosition',(current+1)+' of '+lessons.length);
    $('lessonPrevious').disabled=current===0;$('lessonNext').disabled=current===lessons.length-1;
    nav.forEach((b,i)=>b.setAttribute('aria-current',String(i===current)));
  }
  $('tutorialEditor').oninput=()=>{drafts[lessons[current].id]=$('tutorialEditor').value;save();epoch++;text('tutorialStatus','Edited. Check this version to get fresh feedback.');$('tutorialOutput').hidden=true;text('tutorialRaw','');};
  $('tutorialReset').onclick=()=>{delete drafts[lessons[current].id];save();display();};
  $('lessonPrevious').onclick=()=>{location.hash='learn/'+lessons[current-1].id;};
  $('lessonNext').onclick=()=>{location.hash='learn/'+lessons[current+1].id;};
  $('tutorialRun').onclick=async()=>{
    if(running)return;
    const source=$('tutorialEditor').value,ticket=epoch,l=lessons[current];running=true;$('tutorialRun').disabled=true;
    const started=performance.now();let phase='Starting Lean…';
    const progress=s=>{phase=s;if(ticket===epoch)text('tutorialStatus',s);};
    const timer=setInterval(()=>{if(ticket===epoch)text('tutorialStatus',phase+' · '+Math.round((performance.now()-started)/1000)+' s');},1000);
    try{
      const result=await checkLean(source,progress);if(ticket!==epoch)return;
      const placeholder=hasProofPlaceholder(result);
      text('tutorialStatus',placeholder?'Proof placeholder detected. Replace sorry with a proof.':result.accepted?'Lean accepted this file.':l.expected==='reject'&&source===l.source?'Lean rejected this claim, as expected. Try repairing it.':'Lean did not accept this file. Read the remaining goal or error below.');
      const diagnostics=result.stdout.split('\n').flatMap(line=>{try{const m=JSON.parse(line);return m.severity?[`${m.severity}${m.pos?' · line '+m.pos.line:''}\n${m.data||m.message||''}`]:[];}catch{return line?[line]:[];}}).join('\n\n');
      $('tutorialOutput').hidden=false;text('tutorialOutput',diagnostics||result.stderr||'No printed output. All declarations in this file were checked.');text('tutorialRaw',JSON.stringify(result,null,2));
    }catch(e){if(ticket===epoch)text('tutorialStatus',e.message);}
    finally{clearInterval(timer);running=false;$('tutorialRun').disabled=false;}
  };
  $('tutorialEditor').onkeydown=e=>{if(e.key==='Enter'&&(e.ctrlKey||e.metaKey)){e.preventDefault();$('tutorialRun').click();}};
  $('tutorialDownload').onclick=()=>{const url=URL.createObjectURL(new Blob([$('tutorialEditor').value],{type:'text/plain'}));const a=document.createElement('a');a.href=url;a.download=lessons[current].id+'.lean';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);};
  window.addEventListener('hashchange',display);display();
}
