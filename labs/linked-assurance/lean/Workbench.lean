module
public import Init

@[expose] public section

/-!
Application evidence boundary, NOT a second RDF semantics.
Factoidal owns parsing, RDF term equality and inference. `Claim` records an
untrusted ASK observation over the exact selected graph identified by `Context`.
No constructor here proves that an ASK answer is sound or complete for RDF.
-/
namespace LinkedAssurance

inductive Execution where
  | completed | timeout | parserError | engineFault | cancelled | unsupported
  deriving Repr, DecidableEq, BEq

inductive Knowledge where
  | entailed | notEstablished | unsupported
  deriving Repr, DecidableEq, BEq

inductive Decision where
  | permit | deny | defer | escalate | protectiveShutdown
  deriving Repr, DecidableEq, BEq

inductive AttackOutcome where
  | achieved | notAchieved | unknown
  deriving Repr, DecidableEq, BEq

structure Context where
  datasetBytesSha256 : String
  selectedGraphSha256 : String
  scope : String
  regime : String
  runtimeVersion : String
  deriving Repr, DecidableEq

/-- Application keys bind to exact query text, not to an implicit vocabulary. -/
structure QueryBinding where
  key : String
  query : String
  deriving Repr, DecidableEq

/-- A host observation. This type does not prove query evaluation correct. -/
structure QueryObservation where
  query : String
  answer : Bool
  deriving Repr, DecidableEq

structure Claim where
  key : String
  query : String
  answer : Bool
  deriving Repr

structure Evidence where
  context : Context
  execution : Execution
  claims : List Claim
  deriving Repr

def claimBindings (claims : List Claim) : List QueryBinding :=
  claims.map (fun c => ⟨c.key, c.query⟩)

def claimObservations (claims : List Claim) : List QueryObservation :=
  claims.map (fun c => ⟨c.query, c.answer⟩)

/-- The adapter preserves both input lists, their order, and the execution
context. It rejects repeated keys, mismatched queries and truncated inputs.
Non-completed runs cannot carry claims. This is an envelope contract, not
an RDF entailment claim or a proof of the JavaScript transport. -/
def adapterRequirements (ctx : Context) (execution : Execution)
    (bindings : List QueryBinding) (observations : List QueryObservation)
    (e : Evidence) : Prop :=
  e.context = ctx ∧ e.execution = execution ∧
  claimBindings e.claims = bindings ∧ claimObservations e.claims = observations ∧
  (bindings.map QueryBinding.key).Nodup ∧
  (execution ≠ .completed → e.claims = [])

instance (ctx : Context) (execution : Execution)
    (bindings : List QueryBinding) (observations : List QueryObservation)
    (e : Evidence) : Decidable (adapterRequirements ctx execution bindings observations e) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def adaptEvidence (ctx : Context) (execution : Execution)
    (bindings : List QueryBinding) (observations : List QueryObservation) : Except String Evidence :=
  let claims := List.zipWith (fun b o => Claim.mk b.key b.query o.answer) bindings observations
  let e : Evidence := ⟨ctx, execution, claims⟩
  if adapterRequirements ctx execution bindings observations e then .ok e
  else .error "Query bindings and observations do not satisfy the policy adapter contract"

theorem adaptEvidence_contract (ctx : Context) (execution : Execution)
    (bindings : List QueryBinding) (observations : List QueryObservation)
    (e : Evidence) (h : adaptEvidence ctx execution bindings observations = .ok e) :
    adapterRequirements ctx execution bindings observations e := by
  simp only [adaptEvidence] at h
  split at h
  next hc => cases h; exact hc
  next => contradiction

def Evidence.established (e : Evidence) (key : String) : Bool :=
  decide (e.execution = .completed) && e.claims.any (fun c => c.key == key && c.answer)

/-- A failed ASK is not turned into a semantic refutation. -/
def knowledge (e : Evidence) (key : String) : Knowledge :=
  if e.execution = .unsupported then .unsupported
  else if e.established key then .entailed else .notEstablished

structure OperationalState where
  credentialVerified : Bool
  observedTime : Nat
  expiresAt : Nat
  secureTransportObserved : Bool
  permissionGranted : Bool
  attackerWantsInterruption : Bool
  legitimateSession : Bool
  deriving Repr

/-- Necessary conditions of a permit. A verified demo signature authenticates
only its displayed payload under its displayed key, not a real-world identity. -/
def permitRequirements (e : Evidence) (s : OperationalState) : Prop :=
  e.execution = .completed ∧
  (e.context.regime = "RDFS" ∨ e.context.regime = "simple") ∧
  s.credentialVerified = true ∧ s.observedTime < s.expiresAt ∧
  s.secureTransportObserved = true ∧ s.permissionGranted = true

instance (e : Evidence) (s : OperationalState) : Decidable (permitRequirements e s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def ready (e : Evidence) (s : OperationalState) : Bool := decide (permitRequirements e s)

theorem ready_sound (e : Evidence) (s : OperationalState) (h : ready e s = true) :
    permitRequirements e s := of_decide_eq_true h

def attackerOutcome (d : Decision) (s : OperationalState) : AttackOutcome :=
  if s.attackerWantsInterruption && s.legitimateSession then
    if d = .protectiveShutdown then .achieved else .notAchieved
  else .unknown

theorem timeout_no_negative (e : Evidence) (key : String) (h : e.execution = .timeout) :
    knowledge e key = .notEstablished := by
  simp [knowledge, Evidence.established, h]

theorem shutdown_can_be_attacker_success (s : OperationalState)
    (h₁ : s.attackerWantsInterruption = true) (h₂ : s.legitimateSession = true) :
    attackerOutcome .protectiveShutdown s = .achieved := by
  simp [attackerOutcome, h₁, h₂]

/-- Source terms remain runtime identifiers. Renaming query keys consistently
does not need a Lean class declaration. This is a lookup lemma, not an RDF
renaming theorem; Factoidal's RDF semantics are not redefined here. -/
theorem established_single_claim (ctx : Context) (key query : String) :
    (Evidence.mk ctx .completed [⟨key, query, true⟩]).established key = true := by
  simp [Evidence.established]

end LinkedAssurance
