#!/usr/bin/env python3
"""Produce a same-origin smaller-export Lean 4.33.1 WASM from the ALREADY
mirrored and hash-pinned full Dickory binary. No changes to executable Wasm
code sections: only remove export table entries unused by the browser host.

This is an experiment, NOT equivalent to cauli's separately relinked slim
binary, and proof compilation on an actual iPhone remains an explicit gate.
"""
from __future__ import annotations
import hashlib,json,pathlib,re

LAB=pathlib.Path(__file__).resolve().parents[1]
LINKED=LAB.parent/"linked-assurance"
ART=LAB/"artifacts"
ART.mkdir(parents=True,exist_ok=True)
PIN="4f9018a62ead9be0ffd652021d5afc8501e92253"
SHA="e24b3c712f59e983d7c805d5cc3faddd615398e820d27950834c9a3aa9e74151"
EXPECTED_BYTES=92686390
EXPECTED_SHA="bd41c4ca897a3f78ba41893002d0734051a02036dab65e6d2b7da6c2ca7d8ee7"
EXPECTED_EXPORTED=15952

def leb(data,pos):
    val=0;shift=0;start=pos
    while True:
        if pos>=len(data) or pos-start>6:raise ValueError("Corrupt LEB128")
        b=data[pos];pos+=1
        val|=(b&127)<<shift;shift+=7
        if not b&128:return val,pos

def encode_leb(value):
    output=bytearray()
    while True:
        b=value&127;value>>=7
        if value:output.append(b|128)
        else:output.append(b);return bytes(output)

def hash_bytes(data):return hashlib.sha256(data).hexdigest()

def main():
    pin=json.loads((LINKED/"compiler-assets.json").read_text())
    wasm=(LINKED/pin["lean.wasm"]["url"]).read_bytes()
    if (len(wasm)!=pin["lean.wasm"]["bytes"] or hash_bytes(wasm)!=SHA or
        pin["lean.wasm"]["sha256"]!=SHA):
        raise SystemExit("Original Lean WASM no longer matches pinned source")
    if wasm[:8]!=b"\0asm\x01\0\0\0":raise SystemExit("Not a core WebAssembly module")
    js=(LINKED/"artifacts/lean-browser.js").read_text()
    if hash_bytes(js.encode())!=pin["lean.js"]["browser"]["sha256"]:
        raise SystemExit("Compiled JS browser glue has changed")
    # Only direct low-level runtime calls, plus glue-used locals. The
    # compactor's browser JS iterates over available WASM exports rather
    # than hardcoding 105k method names.
    referenced=set(re.findall(r'wasmExports\["([^"]+)"\]',js))
    worker=(LINKED/"compiler-worker.js").read_text()
    referenced.update(re.findall(r'\bModule\._([a-zA-Z_][a-zA-Z_0-9]*)',worker))
    referenced.update({
        "lean_main","__main_argc_argv",
        "malloc","free","lean_wasm_compile","lean_mk_string",
        "lean_initialize_runtime_module","lean_initialize",
        "lean_io_mark_end_initialization","lean_init_task_manager_using",
        "lean_enable_initializer_execution","lean_init_search_path",
        "lean_io_result_show_error","emscripten_runtime_keepalive_push",
    })
    out=bytearray(wasm[:8]);ptr=8;found=False;names=set();kept=set()
    other_sections=[]
    while ptr<len(wasm):
        start=ptr;kind=wasm[ptr];ptr+=1
        length,ptr=leb(wasm,ptr)
        finish=ptr+length
        if finish>len(wasm):raise SystemExit("Invalid WASM section length")
        payload=wasm[ptr:finish]
        if kind!=7:
            out.extend(wasm[start:finish])
            other_sections.append((kind,hash_bytes(wasm[start:finish])))
        else:
            if found:raise SystemExit("Duplicate WASM export section")
            found=True
            count,pos=leb(payload,0)
            entries=[]
            for _ in range(count):
                begin=pos
                n,pos=leb(payload,pos)
                raw=payload[pos:pos+n]
                if len(raw)!=n:raise SystemExit("Truncated WASM export name")
                name=raw.decode("utf8");pos+=n
                ekind=payload[pos];pos+=1
                _,pos=leb(payload,pos)
                names.add(name)
                # Follow the upstream slim *intent* conservatively: discard
                # generated boxed wrappers, but retain ordinary public Lean
                # functions, C ABI routines, all non-function exports, plus
                # any symbols actually needed by the existing browser host.
                # Keeping non-boxed functions supports runtime calls by name.
                boxed=(name.endswith("___boxed") or name.endswith("_boxed"))
                if ekind!=0 or name in referenced or name.startswith("lean_") or not boxed:
                    entries.append(payload[begin:pos]);kept.add(name)
            if pos!=len(payload):raise SystemExit("Trailing bytes in export section")
            extra=referenced-names
            # Some source symbols are Emscripten JS-only; don't mistake
            # their absence from the WASM export table for a binary error.
            required={"lean_main","lean_wasm_compile","lean_mk_string","lean_initialize",
                "lean_initialize_runtime_module","lean_init_search_path","__indirect_function_table"}
            if missing:=required-names:raise SystemExit("Required WASM ABI missing: "+str(sorted(missing)))
            modified=encode_leb(len(entries))+b"".join(entries)
            out.extend(bytes([kind])+encode_leb(len(modified))+modified)
            print("Pruned "+str(count)+" exports to "+str(len(entries))+"; JS-only names: "+str(len(extra)))
        ptr=finish
    if not found:raise SystemExit("WASM had no export section")
    if len(kept)>=len(names):raise SystemExit("No exports were pruned")
    dest=ART/"lean-slim.wasm"
    dest.write_bytes(out)
    actual={"bytes":dest.stat().st_size,"sha256":hash_bytes(out)}
    if (actual["bytes"] != EXPECTED_BYTES or actual["sha256"] != EXPECTED_SHA or
        len(kept) != EXPECTED_EXPORTED):
        raise SystemExit("Reduced-export WASM drifted from reviewed 4.33.1 result")
    # Lean 4 compiler source is unchanged (same WASM sections except exports).
    report={
        "sourceCommit":PIN,"leanVersion":"4.33.1",
        "inputWasmSha256":SHA,
        "outputWasm":actual,"retainedExports":sorted(kept),
        "retainedCount":len(kept),"removedCount":len(names-kept),
        "unmodifiedSectionHashes":other_sections,
        "transformation":"Remove unreferenced generated boxed-function exports only; preserve all other WebAssembly sections byte-for-byte",
    }
    (ART/"slim-transform.json").write_text(json.dumps(report,indent=2)+"\n")
    manifest={
        "sourceCommit":PIN,"leanVersion":"4.33.1",
        "factoidalPin":"leanprover/lean4:v4.33.1",
        "runtime":{
            "lean.js":{
                "url":"./artifacts/lean-browser.js",
                "bytes":pin["lean.js"]["browser"]["bytes"],
                "sha256":pin["lean.js"]["browser"]["sha256"]
            },
            "lean.wasm":{"url":"../company-accounts/artifacts/lean-slim.wasm",**actual},
            "lean-lib.tar.gz":{
                "url":"./artifacts/toolchain-4.33.1/lean-lib.tar.gz",
                "bytes":pin["lean-lib.tar.gz"]["bytes"],
                "sha256":pin["lean-lib.tar.gz"]["sha256"]
            },
        },
    }
    (ART/"slim-compiler-assets.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print(json.dumps({"status":"pass","oldWasmBytes":len(wasm),"newWasmBytes":len(out),
                      "exported":len(kept),"removed":len(names-kept),
                      "sha256":actual["sha256"]},indent=2))

if __name__=="__main__":main()
