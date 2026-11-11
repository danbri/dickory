import Init

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
  deriving Repr

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
