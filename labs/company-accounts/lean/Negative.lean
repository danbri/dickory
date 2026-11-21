import Accounts

open SWADAccounts

/- This exact concrete equality is FALSE. CI requires Lean to reject it. -/
example : sameExactValue (acidTest fixture) (archivedN3AcidTest fixture) := by
  decide
