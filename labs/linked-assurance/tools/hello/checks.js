// Minimal checks shared by Node, Deno and a real browser worker.
// Runtime initialization/UInt32 decoding follows cauli/lean4's Apache-2.0
// tests/wasm/checks.cjs at 4f9018a62ead9be0ffd652021d5afc8501e92253.
globalThis.leanHello = {
  cases:[
    ['version','#eval Lean.versionString',0,/4\.33\.1/],
    ['hello','#eval "Hello from Lean"',0,/^"Hello from Lean"$/],
    ['arithmetic','#eval 2 + 2',0,/^4$/],
    ['proof','theorem hello (n : Nat) : n + 0 = n := by rfl\n#print axioms hello',0,/does not depend on any axioms/],
    ['false theorem','example : (2 : Nat) + 2 = 5 := by rfl',1,null],
    ['recovery after rejection','#eval 6 * 7',0,/^42$/],
    ['library executable code','#eval ([1, 2, 3] : List Nat).reverse',0,/^\[3, 2, 1\]$/],
  ],
  initialize(M) {
    M._lean_initialize_runtime_module();
    M._lean_initialize();
    M._lean_io_mark_end_initialization();
    M._lean_init_task_manager();
    M._lean_enable_initializer_execution();
    const r=M._lean_init_search_path();
    if((M.getValue(r+7,'i8')&255)!==0)throw Error('Lean search-path initialization failed');
    M._emscripten_runtime_keepalive_push?.();
  },
  async run(M, takeDiagnostics, progress=()=>{}) {
    const string=s=>{const p=M.stringToNewUTF8(s),o=M._lean_mk_string(p);M._free(p);return o;};
    const cases=this.cases;
    const results=[];
    for(const [name,source,wanted,output] of cases){
      // Reuse must survive returning to the host event loop between requests.
      await new Promise(resolve=>setTimeout(resolve,0));
      progress(name);takeDiagnostics();const start=performance.now();
      const r=M._lean_wasm_compile(string(source),string('Hello.lean'));
      if((M.getValue(r+7,'i8')&255)!==0){M._lean_io_result_show_error(r);throw Error(name+': compiler IO failure');}
      // IO success and the enclosed compiler status are separate checks.
      const box=M.getValue(r+8,'i32')>>>0,exitCode=M.getValue(box+8,'i32')>>>0;
      const diagnostics=takeDiagnostics();
      if(exitCode!==wanted || diagnostics.some(d=>d.severity==='error')!==(wanted!==0)
        || output&&!diagnostics.some(d=>output.test(d.data)))
        throw Error(name+': unexpected result '+JSON.stringify({exitCode,diagnostics}));
      results.push({name,source,exitCode,milliseconds:Math.round(performance.now()-start),diagnostics});
    }
    return results;
  }
};
