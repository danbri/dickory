# Veil lab: IKL statements as invariants of a transition system

An experiment in using [Veil](https://github.com/verse-lab/veil) (Apache-2.0), a TLA+-style
framework for transition systems embedded in Lean 4, as glue between formalisms: here, between
a state machine and Common Logic / IKL.

The system is a cache of facts claimed by named graphs. A graph claims propositions
("graph g says p", IKL's `(ist g (that p))`), a graph is trusted or not, and the cache holds
propositions so that queries need not re-read the graphs. The rule: a proposition is cached
only while some trusted graph claims it; retracting a claim or withdrawing trust drops what it
supported.

- [`IstCache/Proof.lean`](IstCache/Proof.lean) states the rule as a first-order invariant over
  any number of graphs and propositions, and Veil's `#check_invariants` proves it inductive.
  Every SMT answer is turned into a kernel-checked proof (`veil.smt.trust false`): nothing rests
  on the solver.
- [`IstCache/Ikl.lean`](IstCache/Ikl.lean) runs the same system on a finite instance (two
  graphs, two propositions) with its invariants written as IKL sentences in CLIF text, for
  example `(forall (p) (if (Cached p) (exists (g) (and (Trusted g) (ist g p)))))` and one with a
  `that`-term, `(if (Cached (that (Blue sky))) (exists (g) (and (Trusted g) (ist g (that (Blue sky))))))`.
  Each is read by factoidal-core's CLIF reader and decided in every reachable state by its
  executable IKL satisfaction checker (`L4Factoidal.CL.FiniteSat`), over an interpretation
  built from the state. `#model_check` visits all reachable states: evidence for this
  instance, not a proof.
- [`IstCache/Audit.lean`](IstCache/Audit.lean) lists every theorem of the lab with the axioms
  its proof uses.

What is proved: the first-order cache rule, for all sizes. What is checked, not proved: that
the IKL sentences hold in every reachable state of the two-by-two instance, and that they
agree there with the first-order form (both are model checked in the same run). Not attempted
yet: a theorem that the IKL sentence's satisfaction equals the first-order formula for every
state (that would go through the agreement of `FiniteSat.sat` with `CL.Semantics.Sat`, which
factoidal-core proves for terms and tests for sentences).

## Toolchain and sources

Veil pins Lean **4.35.0**, so this lab has its own `lean-toolchain`, apart from the 4.33.1
labs. The Common Logic and IKL modules are factoidal-core's (Apache-2.0), at the commit in
[`tools/core-ref.txt`](tools/core-ref.txt), fetched by `tools/fetch_core.sh` into
`artifacts/` (not committed) and compiled here. Veil's dependencies are all Apache-2.0 and do
not include Mathlib; lean-cvc5 downloads a cvc5 binary used by the proof tactics at build time
only.

## Reproduce

```sh
cd labs/veil
./tools/check.sh
```

`check.sh` fetches the pinned sources, runs `lake build` (Veil and its dependencies build from
source the first time), and fails if a check fails, if Veil trusted an SMT answer, if any
theorem rests on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, or if
the audit printed nothing. CI: [`.github/workflows/veil-lab.yml`](../../.github/workflows/veil-lab.yml).
