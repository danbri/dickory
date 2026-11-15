module

public import Veil

/-!
# A cache of facts claimed by named graphs: the first-order invariants, proved

Named graphs claim propositions (`claims g p`: "graph g says p", IKL's `(ist g (that p))`), a
graph can be reliable or not, and a cache holds propositions to answer queries without
re-reading the graphs. The cache rule: a proposition is cached only while some reliable graph
claims it. Retracting a claim or withdrawing trust drops what it supported.

Here the invariants are stated in first-order logic over uninterpreted types and proved
inductive by `#check_invariants` with SMT proof reconstruction (`veil.smt.trust false`).
`IstCache/Ikl.lean` states the same invariants as IKL sentences, read from CLIF text and
decided by factoidal-core's executable IKL checker, over a finite instance.
-/

set_option veil.smt.trust false

veil module IstCacheProof

type graph
type prop

relation claims : graph → prop → Bool
relation reliable : graph → Bool
relation cached : prop → Bool

#gen_state

after_init {
  claims G P := false
  reliable G := false
  cached P := false
}

action claim (g : graph) (p : prop) {
  claims g p := true
}

action endorse (g : graph) {
  reliable g := true
}

-- Cache p only when a reliable graph claims it.
action cache (p : prop) {
  require ∃ g, reliable g ∧ claims g p
  cached p := true
}

-- Retract g's claim of p; drop p from the cache unless another reliable graph claims it.
action retract (g : graph) (p : prop) {
  claims g p := false
  if ¬ (∃ h, h ≠ g ∧ reliable h ∧ claims h p) then
    cached p := false
}

-- Withdraw trust in g; drop every cached proposition no other reliable graph claims.
-- (A two-state transition: over uninterpreted types the post-state of `cached` is not
-- computable, so it is stated as a relation; `IstCache/Ikl.lean` has the same step as an
-- action over the finite instance.)
transition revoke {
  ∃ g, (∀ h, reliable' h ↔ (reliable h ∧ h ≠ g)) ∧
    (∀ p, cached' p ↔ (cached p ∧ ∃ h, h ≠ g ∧ reliable h ∧ claims h p))
}

-- (forall (p) (if (Cached p) (exists (g) (and (Trusted g) (ist g p)))))
safety [cache_sound] cached P → ∃ g, reliable g ∧ claims g P

#gen_spec

-- `revoke` is a relational step, which the SMT translation does not take; its verification
-- condition is proved by hand: what stays cached is claimed by a graph that stays reliable.
prove_veil_invariant_goal revoke cache_sound using tr by
  obtain ⟨hframe, g, hr, hc⟩ := htr
  intro hcP
  obtain ⟨_, h, hne, hrel, hcl⟩ := (hc P).1 hcP
  exact ⟨h, (hr h).2 ⟨hrel, hne⟩, (hframe h P) ▸ hcl⟩

#check_invariants

#gen_theorems

end IstCacheProof
