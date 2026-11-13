module
public import Init
@[expose] public section
namespace LinkedAssurance.DeveloperProfile

/-! Semantics of the portable developer profile, not of MCP/HTTP/JavaScript.
The JSON parser, JSON Schema predicate, host effects and runtime remain separate
refinement obligations. Values and validation predicates are parameters. -/
inductive DecodeError where
  | missingRequired | invalidValue
  deriving Repr, DecidableEq

structure Field (Value : Type) where
  required : Bool
  accepts : Value → Bool
  defaultValue : Option Value

def checked (f : Field V) (v : V) : Except DecodeError (Option V) :=
  if f.accepts v then .ok (some v) else .error .invalidValue

/-- Absence is not null. Required fields cannot be filled by a default. -/
def resolve (f : Field V) (input : Option V) : Except DecodeError (Option V) :=
  match input with
  | some v => checked f v
  | none =>
    if f.required then .error .missingRequired
    else match f.defaultValue with
      | some v => checked f v
      | none => .ok none

theorem required_missing (f : Field V) (h : f.required = true) :
    resolve f none = .error .missingRequired := by simp [resolve, h]

theorem optional_without_default (f : Field V)
    (hr : f.required = false) (hd : f.defaultValue = none) :
    resolve f none = .ok none := by simp [resolve, hr, hd]

theorem supplied_overrides_default (f : Field V) (v : V) :
    resolve f (some v) = checked f v := rfl

theorem checked_sound (f : Field V) (v out : V)
    (h : checked f v = .ok (some out)) : f.accepts out = true := by
  unfold checked at h
  split at h
  next ha => cases h; exact ha
  next => contradiction

theorem resolve_sound (f : Field V) (input : Option V) (v : V)
    (h : resolve f input = .ok (some v)) : f.accepts v = true := by
  cases input with
  | some x => exact checked_sound f x v h
  | none =>
    simp only [resolve] at h
    split at h
    next => contradiction
    next =>
      cases hd : f.defaultValue with
      | none => simp [hd] at h
      | some x => simp only [hd] at h; exact checked_sound f x v h

/-- Once defaulted/validated, resubmission as a supplied value is stable. -/
theorem resolved_value_idempotent (f : Field V) (input : Option V) (v : V)
    (h : resolve f input = .ok (some v)) : resolve f (some v) = .ok (some v) := by
  have valid := resolve_sound f input v h
  simp [resolve, checked, valid]

inductive Transport where
  | stdio | streamableHttp | webmcp | localCli
  deriving Repr, DecidableEq
structure Profile where
  enabledTools : List String
  transports : List Transport
  maxBudget : Nat
structure Tool where
  name : String
  requires : List String

def Allowed (p : Profile) (caps : List String) (t : Transport)
    (tool : Tool) (budget : Nat) : Prop :=
  tool.name ∈ p.enabledTools ∧ t ∈ p.transports ∧
  tool.requires.all (fun c => decide (c ∈ caps)) = true ∧ budget ≤ p.maxBudget
instance (p : Profile) (caps : List String) (t : Transport)
    (tool : Tool) (budget : Nat) : Decidable (Allowed p caps t tool budget) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def admit (p : Profile) (caps : List String) (t : Transport)
    (tool : Tool) (budget : Nat) : Bool := decide (Allowed p caps t tool budget)

theorem admission_sound (p : Profile) (caps : List String) (t : Transport)
    (tool : Tool) (budget : Nat) (h : admit p caps t tool budget = true) :
    Allowed p caps t tool budget := of_decide_eq_true h

theorem admitted_capabilities (p : Profile) (caps : List String) (t : Transport)
    (tool : Tool) (budget : Nat) (h : admit p caps t tool budget = true) :
    ∀ c ∈ tool.requires, c ∈ caps := by
  intro c hc
  have ha := admission_sound p caps t tool budget h
  exact of_decide_eq_true ((List.all_eq_true.mp ha.2.2.1) c hc)

theorem disabled_tool_rejected (p : Profile) (caps : List String) (t : Transport)
    (tool : Tool) (budget : Nat) (h : tool.name ∉ p.enabledTools) :
    admit p caps t tool budget = false := by simp [admit, Allowed, h]

theorem disabled_transport_rejected (p : Profile) (caps : List String) (t : Transport)
    (tool : Tool) (budget : Nat) (h : t ∉ p.transports) :
    admit p caps t tool budget = false := by simp [admit, Allowed, h]

theorem missing_capability_rejected (p : Profile) (caps : List String)
    (t : Transport) (tool : Tool) (budget : Nat) (c : String)
    (hr : c ∈ tool.requires) (hm : c ∉ caps) :
    admit p caps t tool budget = false := by
  have h : ¬ Allowed p caps t tool budget := by
    intro ha
    have hc : decide (c ∈ caps) = true := (List.all_eq_true.mp ha.2.2.1) c hr
    exact hm (of_decide_eq_true hc)
  simp [admit, h]

/-- A narrower exposure/resource policy cannot create a new admissible call. -/
theorem restriction_monotone (small large : Profile) (caps : List String)
    (t : Transport) (tool : Tool) (budget : Nat)
    (hn : ∀ n ∈ small.enabledTools, n ∈ large.enabledTools)
    (ht : ∀ x ∈ small.transports, x ∈ large.transports)
    (hb : small.maxBudget ≤ large.maxBudget)
    (h : Allowed small caps t tool budget) : Allowed large caps t tool budget :=
  ⟨hn _ h.1, ht _ h.2.1, h.2.2.1, Nat.le_trans h.2.2.2 hb⟩

/-- Transport metadata is erased before evaluating an already resolved call.
Actual JS/Node/browser decoding agreement is tested, not assumed proven here. -/
def application (handler : A → R) (_transport : Transport) (args : A) : R := handler args

theorem transport_independent_result (handler : A → R) (a b : A)
    (t u : Transport) (h : a = b) : application handler t a = application handler u b := by
  cases h
  rfl

/-- Resource faults have no fabricated negative semantic answer. -/
inductive RunResult (A : Type) where
  | completed (value : A)
  | timeout | cancelled | unavailable | fault
  deriving Repr

def answers : RunResult (List Bool) → List Bool
  | .completed xs => xs
  | _ => []

theorem timeout_has_no_answers : answers .timeout = [] := rfl
theorem cancelled_has_no_answers : answers .cancelled = [] := rfl

#print axioms required_missing
#print axioms resolve_sound
#print axioms resolved_value_idempotent
#print axioms admission_sound
#print axioms admitted_capabilities
#print axioms restriction_monotone
#print axioms transport_independent_result
end LinkedAssurance.DeveloperProfile
