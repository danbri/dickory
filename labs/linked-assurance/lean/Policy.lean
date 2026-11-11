module
public import Workbench

@[expose] public section
open LinkedAssurance

namespace LinkedAssurance

/-- Edit this function and its contract together. Claim keys are ASK bindings
in Queries.json. A positive classification alone never grants permission. -/
def policy (e : Evidence) (s : OperationalState) : Decision :=
  if e.execution != .completed then .defer
  else if e.established "alert" then .protectiveShutdown
  else if e.established "organization" && e.established "disjointnessAssertion" then .escalate
  else if !e.established "classification" then .defer
  else if e.established "reviewRequired" then .escalate
  else if !e.established "applicationCondition" then .defer
  else if ready e s then .permit else .deny

/-- This obligation refers to the actual executable `policy` above. It is
conditional on injected evidence and external observations. -/
theorem policy_contract (e : Evidence) (s : OperationalState)
    (h : policy e s = .permit) : permitRequirements e s := by
  unfold policy at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  next hr => exact ready_sound e s hr
  next => contradiction

theorem permit_requires_verified_credential (e : Evidence) (s : OperationalState)
    (h : policy e s = .permit) : s.credentialVerified = true :=
  (policy_contract e s h).2.2.1

theorem permit_requires_unexpired (e : Evidence) (s : OperationalState)
    (h : policy e s = .permit) : s.observedTime < s.expiresAt :=
  (policy_contract e s h).2.2.2.1

/-- Successful adaptation and permission compose their contracts. The inputs
are still host observations, not a proof of the external query execution. -/
theorem policy_pipeline_contract (ctx : Context) (execution : Execution)
    (bindings : List QueryBinding) (observations : List QueryObservation)
    (e : Evidence) (s : OperationalState)
    (ha : adaptEvidence ctx execution bindings observations = .ok e)
    (hp : policy e s = .permit) :
    adapterRequirements ctx execution bindings observations e ∧ permitRequirements e s :=
  ⟨adaptEvidence_contract ctx execution bindings observations e ha, policy_contract e s hp⟩

end LinkedAssurance
