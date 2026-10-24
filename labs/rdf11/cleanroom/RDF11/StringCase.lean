/-
ASCII case conversion used by RDF 1.1 language-tag values.
This changes neither non-ASCII characters nor literal lexical forms.
-/
import RDF11.Datatypes
import Init.Data.String.Lemmas.Modify

namespace RDF11

theorem charLower_idempotent (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split
  · rename_i h
    split
    · rename_i hbad
      have hhigh := h.2
      have hlow := h.1
      have hbad' := hbad.2
      change c.val.toNat ≤ 90 at hhigh
      change 65 ≤ c.val.toNat at hlow
      change (c.val + (97 - 65 : UInt32)).toNat ≤ 90 at hbad'
      simp only [UInt32.toNat_add] at hbad'
      change (c.val.toNat + 32) % 4294967296 ≤ 90 at hbad'
      omega
    · rfl
  · rfl

theorem asciiLower_idempotent (s : String) : asciiLower (asciiLower s) = asciiLower s := by
  simp only [asciiLower, String.map_map]
  congr 1
  funext c
  exact charLower_idempotent c

end RDF11
