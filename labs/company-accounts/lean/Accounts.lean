import Init

/-!
SWAD-Europe company accounts, reconstructed as an *explicitly chosen* reference
semantics rather than a claim that the 2004 data units were correct.
All monetary inputs are integer minor units (pence), from one currency, for one
reporting period. A returned pair (numerator, denominator) is an EXACT rational
value, not an integer division or floating point approximation. `none` denotes
a zero denominator. The UI must never silently render it as zero.
-/

namespace SWADAccounts

structure Money where
  pence : Int
  deriving Repr, DecidableEq

def gbp (wholePounds : Int) : Money := ⟨100 * wholePounds⟩

structure Accounts where
  operatingProfit : Money
  netAssets : Money
  salesRevenue : Money
  salesPerEmployee : Money
  nonUkSales : Money
  stock : Money
  debtors : Money
  cash : Money
  currentLiabilities : Money
  costOfSales : Money
  employees : Nat
  deriving Repr

/-- Preserve exact rational arithmetic and make division by zero explicit. -/
def exactRatio (numerator denominator : Int) : Option (Int × Int) :=
  if denominator = 0 then none else some (numerator, denominator)

/-- Semantic equality of optional exact ratios. Fractions are compared by
cross-multiplication, never by structural equality of unreduced pairs. -/
def sameExactValue (lhs rhs : Option (Int × Int)) : Prop :=
  match lhs, rhs with
  | none, none => True
  | some x, some y => x.1 * y.2 = y.1 * x.2
  | _, _ => False

/-- Percent: operating profit / net assets × 100. -/
def returnOnNetAssets (a : Accounts) : Option (Int × Int) :=
  exactRatio (100 * a.operatingProfit.pence) a.netAssets.pence

/-- Percent: operating profit / sales revenue × 100. -/
def profitMargin (a : Accounts) : Option (Int × Int) :=
  exactRatio (100 * a.operatingProfit.pence) a.salesRevenue.pence

/-- Dimensionless: sales revenue / net assets. -/
def assetTurnover (a : Accounts) : Option (Int × Int) :=
  exactRatio a.salesRevenue.pence a.netAssets.pence

/-- A rational headcount estimate; integrality is NOT assumed. -/
def estimatedEmployees (a : Accounts) : Option (Int × Int) :=
  exactRatio a.salesRevenue.pence a.salesPerEmployee.pence

/-- Pence per person; a zero employee count is undefined. -/
def operatingProfitPerEmployee (a : Accounts) : Option (Int × Int) :=
  exactRatio a.operatingProfit.pence (Int.ofNat a.employees)

/-- Percent of sales earned outside the UK. -/
def nonUkSalesRatio (a : Accounts) : Option (Int × Int) :=
  exactRatio (100 * a.nonUkSales.pence) a.salesRevenue.pence

/-- Current assets: in this intentionally restricted schema only
stock + debtors + cash. Other accounting classifications are out of scope. -/
def currentAssets (a : Accounts) : Money :=
  ⟨a.stock.pence + a.debtors.pence + a.cash.pence⟩

def currentRatio (a : Accounts) : Option (Int × Int) :=
  exactRatio (currentAssets a).pence a.currentLiabilities.pence

/-- The acid test deliberately excludes stock. -/
def acidTest (a : Accounts) : Option (Int × Int) :=
  exactRatio (a.debtors.pence + a.cash.pence) a.currentLiabilities.pence

/-- Modern DSO convention adopted FOR THIS LAB: debtors / annual sales × 365.
The original SWAD example used a different scaling expression; see below. -/
def debtorDays (a : Accounts) (daysInPeriod : Nat := 365) : Option (Int × Int) :=
  exactRatio (a.debtors.pence * Int.ofNat daysInPeriod) a.salesRevenue.pence

/-- Modern DIO convention adopted FOR THIS LAB: stock / annual cost of sales × 365. -/
def stockDays (a : Accounts) (daysInPeriod : Nat := 365) : Option (Int × Int) :=
  exactRatio (a.stock.pence * Int.ofNat daysInPeriod) a.costOfSales.pence

/- The following are intentionally INCORRECT archive reconstructions.
   They are NOT normative, and must never be quietly substituted for the
   corrected definitions. N3 source provenance is in the inline archive. -/

/-- Archived rule 8 N3 incorrectly includes stock, giving current ratio. -/
def archivedN3AcidTest (a : Accounts) : Option (Int × Int) :=
  exactRatio (a.debtors.pence + a.cash.pence + a.stock.pence) a.currentLiabilities.pence

/-- Archived rule 10 N3 omits the ×100000 factor present in Perl/MathML,
and divides the quotient by 365. Encoded as an exact fraction. -/
def archivedN3DebtorDays (a : Accounts) : Option (Int × Int) :=
  exactRatio a.debtors.pence (a.salesRevenue.pence * 365)

/-- Archived rule 11 conclusion uses the 'dd' predicate, not 'sd'. -/
def archivedStockOutputPredicate : String := "dd"
def stockOutputPredicate : String := "sd"

/- Small independent reference ledger; deliberately not labelled as
   one of the historic companies. Money inputs here are WHOLE GBP. -/
def fixture : Accounts := {
  operatingProfit := gbp 15
  netAssets := gbp 100
  salesRevenue := gbp 200
  salesPerEmployee := gbp 50
  nonUkSales := gbp 20
  stock := gbp 50
  debtors := gbp 40
  cash := gbp 10
  currentLiabilities := gbp 25
  costOfSales := gbp 150
  employees := 4
}

/-- Structural theorem: stock has no influence on the acid test. -/
theorem acid_ignores_stock (a : Accounts) (replacement : Money) :
    acidTest { a with stock := replacement } = acidTest a := by
  rfl

/-- Structural theorem: the three-component model makes stock additive. -/
theorem current_assets_components (a : Accounts) :
    (currentAssets a).pence = a.stock.pence + a.debtors.pence + a.cash.pence := by
  rfl

/-- Explicit boundary value: division by zero must not yield a ratio. -/
theorem acid_undefined_at_zero_liabilities :
    acidTest { fixture with currentLiabilities := gbp 0 } = none := by
  decide

/-- Rule 8's 2004 N3 expression violates the adopted acid-test definition. -/
theorem archived_rule8_counterexample :
    ¬ sameExactValue (acidTest fixture) (archivedN3AcidTest fixture) := by
  decide

/-- Rule 10's archived N3 scaling is not a conventional days-of-sales ratio. -/
theorem archived_rule10_counterexample :
    ¬ sameExactValue (debtorDays fixture) (archivedN3DebtorDays fixture) := by
  decide

/-- Rule 11 emits an incompatible predicate. -/
theorem archived_rule11_predicate_mismatch :
    archivedStockOutputPredicate ≠ stockOutputPredicate := by
  decide

/-- Exact ratios retain their input numerator and denominator. -/
theorem exact_ratio_nonzero (n d : Int) (h : d ≠ 0) :
    exactRatio n d = some (n, d) := by
  simp [exactRatio, h]

/- A genuine rejection example is in Negative.lean; it must fail to compile. -/
#check acid_ignores_stock
#check archived_rule8_counterexample
#print axioms SWADAccounts.current_assets_components
#print axioms SWADAccounts.acid_undefined_at_zero_liabilities
#print axioms SWADAccounts.exact_ratio_nonzero
#print axioms SWADAccounts.acid_ignores_stock
#print axioms SWADAccounts.archived_rule8_counterexample
#print axioms SWADAccounts.archived_rule10_counterexample
#print axioms SWADAccounts.archived_rule11_predicate_mismatch
#eval acidTest fixture
#eval archivedN3AcidTest fixture
#eval debtorDays fixture
#eval stockDays fixture

end SWADAccounts
