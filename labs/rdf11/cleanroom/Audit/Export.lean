/-
Build-time evidence only. Reads elaborated types/bodies and actual module origins.
Not part of RDF semantics; this extractor is an explicitly trusted QA tool.
-/
import RDF11
import Audit
import Lean
open Lean Elab Command

elab "#export_rdf_evidence" : command => do
  let env ← getEnv
  let mut records : Array Json := #[]
  let mut pending : List Name := []
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (Name.mkSimple "RDF11").isPrefixOf m ||
          (Name.mkSimple "Audit").isPrefixOf m then pending := n :: pending
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | throwError "Missing dependency {n}"
    let mut deps := info.type.getUsedConstants
    if let some v := info.value? (allowOpaque := true) then
      deps := deps ++ v.getUsedConstants
    if let .inductInfo v := info then deps := deps ++ v.ctors.toArray
    deps := (deps.toList.mergeSort Name.lt).toArray
    pending := deps.toList ++ pending
    let origin := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "<current-or-kernel>"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let axs ← collectAxioms n
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson origin),
      ("kind", toJson kind), ("unsafe", toJson info.isUnsafe),
      ("type", toJson (← liftTermElabM <| Meta.ppExpr info.type).pretty),
      ("dependencies", toJson (deps.map Name.toString)),
      ("axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("lean_version", toJson Lean.versionString),
    ("declarations", Json.arr (records.qsort fun a b =>
      (a.getObjValAs? String "name").toOption.getD "" <
      (b.getObjValAs? String "name").toOption.getD ""))]
  liftIO <| IO.FS.writeFile "artifacts/declarations.json" (result.pretty ++ "\n")

#export_rdf_evidence

