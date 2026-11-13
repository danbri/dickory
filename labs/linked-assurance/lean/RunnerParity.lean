module
public import Policy
@[expose] public section
namespace LinkedAssurance

/-!
Conditional observational equivalence of the Node and browser CLIs.
This theorem does NOT prove JavaScript, Wasm, transport, or memory safety.
Separate executable tests must establish that the two runners produced
the same context, query bindings, observed booleans and operational state.
-/

/-- Equal evidence and operational states yield equal policy decisions and
attacker-outcome values. -/
theorem policy_runner_parity
    (nodeEvidence browserEvidence : Evidence)
    (nodeState browserState : OperationalState)
    (he : nodeEvidence = browserEvidence)
    (hs : nodeState = browserState) :
    policy nodeEvidence nodeState = policy browserEvidence browserState ∧
    attackerOutcome (policy nodeEvidence nodeState) nodeState =
      attackerOutcome (policy browserEvidence browserState) browserState := by
  cases he
  cases hs
  exact ⟨rfl, rfl⟩

/-- Given equal independently produced contexts, query bindings,
observations and operational state, the checked evidence adapters compose
with the policy and return equal Except results. This does NOT establish
that external engines really produced equal observations. -/
theorem runner_adapter_parity
    (nodeCtx browserCtx : Context)
    (nodeExec browserExec : Execution)
    (nodeBindings browserBindings : List QueryBinding)
    (nodeAnswers browserAnswers : List QueryObservation)
    (nodeState browserState : OperationalState)
    (hc : nodeCtx = browserCtx)
    (hx : nodeExec = browserExec)
    (hb : nodeBindings = browserBindings)
    (ho : nodeAnswers = browserAnswers)
    (hs : nodeState = browserState) :
    (adaptEvidence nodeCtx nodeExec nodeBindings nodeAnswers).map
      (fun e => (policy e nodeState, attackerOutcome (policy e nodeState) nodeState)) =
    (adaptEvidence browserCtx browserExec browserBindings browserAnswers).map
      (fun e => (policy e browserState, attackerOutcome (policy e browserState) browserState)) := by
  cases hc
  cases hx
  cases hb
  cases ho
  cases hs
  rfl

#print axioms LinkedAssurance.policy_runner_parity
#print axioms LinkedAssurance.runner_adapter_parity
end LinkedAssurance
