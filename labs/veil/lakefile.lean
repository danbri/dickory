import Lake
open Lake DSL

/-!
Veil lab: IKL statements as invariants of a transition system.

Veil (https://github.com/verse-lab/veil, Apache-2.0) pins Lean v4.35.0, so this lab has its own
toolchain. The Common Logic / IKL modules come from factoidal-core at the commit pinned in
`tools/core-ref.txt`, fetched by `tools/fetch_core.sh` into `artifacts/factoidal-core` (not
committed) and compiled here with this toolchain.
-/

package veilLab

require veil from git "https://github.com/verse-lab/veil.git" @ "317b2a995170521ddc561ed9f64289c5d545be45"

/-- factoidal-core's CL/IKL modules (Apache-2.0), compiled from the pinned source. -/
lean_lib CoreCL where
  srcDir := "artifacts/factoidal-core/formal/lean4"
  roots := #[]
  globs := #[.one `L4Factoidal.Encoding.Hex, .one `L4Factoidal.Syntax.Lexing,
    .one `L4Factoidal.CL.Syntax, .one `L4Factoidal.CL.Semantics, .one `L4Factoidal.CL.Clif,
    .one `L4Factoidal.CL.Alpha, .one `L4Factoidal.CL.Examples, .one `L4Factoidal.CL.FiniteSat]

@[default_target]
lean_lib IstCache
