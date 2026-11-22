/**
 * Genuine on-device Lean route using cauli/lean4-wasm-in-browser's documented
 * #s= gzip + base64url workspace encoding (small sources only).
 *
 * The source travels in the URL fragment, not a server-side POST.
 * The external browser page still has access to the code through its JS.
 * This link itself is NOT evidence that that compiler accepted the source.
 */
const PLAYGROUND='https://lean.cau.li/?variant=slim';
const MAX_SOURCE_BYTES=250_000;

export const smallLeanProbe = [
  'import Init',
  '',
  'namespace CompanyAccountsPhoneProbe',
  '',
  'structure Accounts where',
  '  stock : Nat',
  '  debtors : Nat',
  '  cash : Nat',
  '  liabilities : Nat',
  '',
  'def acidTest (a : Accounts) : Nat :=',
  '  (a.debtors + a.cash) / a.liabilities',
  '',
  'theorem acid_ignores_stock (a : Accounts) (replacement : Nat) :',
  '    acidTest { a with stock := replacement } = acidTest a := by',
  '  rfl',
  '',
  'theorem two_not_four : (40 + 10 : Nat) / 25 = 2 := by',
  '  decide',
  '',
  '#print axioms CompanyAccountsPhoneProbe.acid_ignores_stock',
  '#print axioms CompanyAccountsPhoneProbe.two_not_four',
  '#eval Lean.versionString',
  '#eval (40 + 10 : Nat) / 25',
  '',
  'end CompanyAccountsPhoneProbe',
  ''
].join('\n');

export async function leanMobileWorkspaceLink(source,name='Accounts.lean'){
  if(typeof source!=='string'||!source.trim())throw Error('Lean source is empty.');
  if(!/^[A-Za-z0-9_.-]+\.lean$/.test(name))throw Error('Invalid mobile Lean filename.');
  const payload=new TextEncoder().encode(JSON.stringify({
    files:[{name,content:source}],active:name
  }));
  if(payload.byteLength>MAX_SOURCE_BYTES)throw Error('Lean source exceeds the mobile-link limit.');
  if(typeof CompressionStream==='undefined')
    throw Error('This browser cannot compress a Lean workspace for a fragment-only link.');
  const stream=new Blob([payload]).stream().pipeThrough(new CompressionStream('gzip'));
  const bytes=new Uint8Array(await new Response(stream).arrayBuffer());
  let binary='';
  for(let i=0;i<bytes.length;i++) binary+=String.fromCharCode(bytes[i]);
  const encoded=btoa(binary).replaceAll('+','-').replaceAll('/','_').replace(/=+$/,'');
  return PLAYGROUND+'#s='+encoded;
}

export async function decodeMobileWorkspaceFragment(fragment){
  // For browser/CI regression checks only. Does not verify a compiler result.
  if(!fragment.startsWith('#s='))throw Error('Not a Lean share fragment');
  const value=fragment.slice(3).replaceAll('-','+').replaceAll('_','/');
  const binary=atob(value);
  const bytes=Uint8Array.from(binary,x=>x.charCodeAt(0));
  if(typeof DecompressionStream==='undefined')throw Error('DecompressionStream unavailable');
  const raw=await new Response(new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();
  return JSON.parse(new TextDecoder().decode(raw));
}
