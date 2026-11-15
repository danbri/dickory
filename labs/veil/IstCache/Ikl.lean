import Veil
import L4Factoidal.CL.FiniteSat

/-!
# The same cache, with its invariants written in IKL

`IstCache/Proof.lean` proves the cache rule as a first-order invariant over any number of graphs
and propositions. Here the system is a finite instance (two named graphs, two propositions) and
its invariants are IKL sentences in CLIF text, read by factoidal-core's CLIF reader
(`L4Factoidal.CL.Clif.parseClifSentence`) and decided in every reachable state by its executable
satisfaction checker (`L4Factoidal.CL.FiniteSat`), over an interpretation built from the state:

- the individuals are the two graphs (10, 11), the two propositions (20, 21) and the relation
  names `ist` (1), `Cached` (2), `Trusted` (3);
- a proposition is the denotation of a `that`-term: `(that (Blue sky))` denotes 20 and
  `(that (Wet rain))` 21 (IKL keys a proposition by the canonical CLIF of its sentence);
- `(ist g p)` holds when graph `g` claims `p`, `(Cached p)` when `p` is cached, `(Trusted g)`
  when `g` is reliable.

`#model_check` visits every reachable state of the instance and evaluates each IKL invariant
there: test evidence over this instance, not a proof. The proof for every size is the
first-order mirror in `Proof.lean`; that the two say the same thing is checked here, by also
model checking the first-order form (`cache_sound_fol`) in the same run, not proved.
-/

namespace IstCacheIkl
open L4Factoidal.CL

abbrev Graph := Fin 2
abbrev Prop' := Fin 2

/-- CLIF text of the proposition each `Prop'` stands for. -/
def propText (p : Prop') : String := if p.val = 0 then "(Blue sky)" else "(Wet rain)"

def graphId (g : Graph) : Nat := 10 + g.val
def propId (p : Prop') : Nat := 20 + p.val

def allGraphs : List Graph := [0, 1]
def allProps : List Prop' := [0, 1]

/-- The finite IKL interpretation of a state. -/
def interp (claims : Graph → Prop' → Bool) (reliable : Graph → Bool) (cached : Prop' → Bool) :
    FiniteInterp Nat where
  domain := [1, 2, 3, 10, 11, 20, 21, 99]
  deflt := 99
  names := [("ist", 1), ("Cached", 2), ("Trusted", 3), ("g0", 10), ("g1", 11)]
  strs := []
  fns := []
  rels :=
    (allGraphs.flatMap fun g => allProps.filterMap fun p =>
      if claims g p then some (1, [graphId g, propId p]) else none) ++
    (allProps.filterMap fun p => if cached p then some (2, [propId p]) else none) ++
    (allGraphs.filterMap fun g => if reliable g then some (3, [graphId g]) else none)
  props := allProps.map fun p =>
    (((parseClifSentence (propText p)).toOption.map Sentence.toClif).getD (propText p), propId p)

/-- An IKL sentence (CLIF text) holds in the state; a sentence that does not parse is false. -/
def holds (text : String) (claims : Graph → Prop' → Bool) (reliable : Graph → Bool)
    (cached : Prop' → Bool) : Bool :=
  match parseClifSentence text with
  | .ok s => (interp claims reliable cached).satisfies s
  | .error _ => false

def cacheSound : String :=
  "(forall (p) (if (Cached p) (exists (g) (and (Trusted g) (ist g p)))))"
def blueSkySupported : String :=
  "(if (Cached (that (Blue sky))) (exists (g) (and (Trusted g) (ist g (that (Blue sky))))))"
def onlyGraphsClaim : String :=
  "(forall (g p) (if (ist g p) (or (= g g0) (= g g1))))"

-- The checker decides both ways on fixed states.
#guard holds cacheSound (fun _ _ => false) (fun _ => false) (fun _ => false)
#guard holds cacheSound (fun _ _ => false) (fun _ => false) (fun p => p.val = 0) == false
#guard holds blueSkySupported (fun g p => g.val = 1 && p.val = 0) (fun g => g.val = 1)
  (fun p => p.val = 0)
#guard holds blueSkySupported (fun g p => g.val = 1 && p.val = 0) (fun g => g.val = 0)
  (fun p => p.val = 0) == false

end IstCacheIkl

open IstCacheIkl

veil module IstCacheModel

relation claims : Graph → Prop' → Bool
relation reliable : Graph → Bool
relation cached : Prop' → Bool

#gen_state

after_init {
  claims G P := false
  reliable G := false
  cached P := false
}

action claim (g : Graph) (p : Prop') {
  claims g p := true
}

action endorse (g : Graph) {
  reliable g := true
}

action cache (p : Prop') {
  require ∃ g, reliable g ∧ claims g p
  cached p := true
}

action retract (g : Graph) (p : Prop') {
  claims g p := false
  if ¬ (∃ h, h ≠ g ∧ reliable h ∧ claims h p) then
    cached p := false
}

action revoke (g : Graph) {
  reliable g := false
  cached P := cached P ∧ (∃ h, h ≠ g ∧ reliable h ∧ claims h P)
}

safety [cache_sound_ikl] holds cacheSound claims reliable cached = true
safety [blue_sky_ikl] holds blueSkySupported claims reliable cached = true
safety [only_graphs_ikl] holds onlyGraphsClaim claims reliable cached = true
safety [cache_sound_fol] cached P → ∃ g, reliable g ∧ claims g P

#gen_spec

#model_check interpreted { } { }

end IstCacheModel
