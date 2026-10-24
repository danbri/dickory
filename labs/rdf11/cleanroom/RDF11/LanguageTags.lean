/-
RDF 1.1 Concepts §3.3 imports BCP47 well-formedness. RFC 5646 §2.1
supplies the grammar; §2.2.9 distinguishes it from registry validity.
The productions below operate after ASCII lowercasing, as ABNF strings
and language tags are case-insensitive. The original spelling is retained.
No registry membership, uniqueness of variants or extension singletons,
preferred spelling, or language-tag matching algorithm is imposed here.
-/
import RDF11.StringCase
import Init.Data.List.SplitOn.Lemmas

namespace RDF11.BCP47

def alpha (c : Char) : Prop := 'a' ≤ c ∧ c ≤ 'z'

def digit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

def alphanum (c : Char) : Prop := alpha c ∨ digit c

def subtag (lo hi : Nat) (kind : Char → Prop) (s : String) : Prop :=
  lo ≤ s.length ∧ s.length ≤ hi ∧ ∀ c ∈ s.toList, kind c

def subtags (lo hi : Nat) (kind : Char → Prop) (ss : List String) : Prop :=
  ∀ s ∈ ss, subtag lo hi kind s

def language (ss : List String) : Prop :=
  (∃ s ext, ss = s :: ext ∧ subtag 2 3 alpha s ∧
    ext.length ≤ 3 ∧ subtags 3 3 alpha ext) ∨
  (∃ s, ss = [s] ∧ subtag 4 4 alpha s) ∨
  (∃ s, ss = [s] ∧ subtag 5 8 alpha s)

def script (s : String) : Prop := subtag 4 4 alpha s

def region (s : String) : Prop := subtag 2 2 alpha s ∨ subtag 3 3 digit s

def variant (s : String) : Prop :=
  subtag 5 8 alphanum s ∨
    (subtag 4 4 alphanum s ∧ ∃ c cs, s.toList = c :: cs ∧ digit c)

def singleton (s : String) : Prop := subtag 1 1 alphanum s ∧ s ≠ "x"

def extension (ss : List String) : Prop :=
  ∃ s rest, ss = s :: rest ∧ singleton s ∧ rest ≠ [] ∧ subtags 2 8 alphanum rest

def privateuse (ss : List String) : Prop :=
  ∃ rest, ss = "x" :: rest ∧ rest ≠ [] ∧ subtags 1 8 alphanum rest

def optionalSubtag (P : String → Prop) (ss : List String) : Prop :=
  ss = [] ∨ ∃ s, ss = [s] ∧ P s

def langtag (ss : List String) : Prop :=
  ∃ l s r vs es p,
    language l ∧ optionalSubtag script s ∧ optionalSubtag region r ∧
    (∀ v ∈ vs, variant v) ∧ (∀ e ∈ es, extension e) ∧
    (p = [] ∨ privateuse p) ∧ ss = l ++ s ++ r ++ vs ++ List.flatten es ++ p

/-- The fixed RFC 5646 alternatives, including both irregular and regular tags. -/
def grandfathered : List String :=
  ["en-gb-oed", "i-ami", "i-bnn", "i-default", "i-enochian", "i-hak", "i-klingon",
   "i-lux", "i-mingo", "i-navajo", "i-pwn", "i-tao", "i-tay", "i-tsu",
   "sgn-be-fr", "sgn-be-nl", "sgn-ch-de", "art-lojban", "cel-gaulish", "no-bok",
   "no-nyn", "zh-guoyu", "zh-hakka", "zh-min", "zh-min-nan", "zh-xiang"]

def parts (s : String) : List String :=
  (s.toList.splitOn '-').map String.ofList

theorem parts_reassemble (s : String) :
    String.ofList (['-'].intercalate ((parts s).map String.toList)) = s := by
  simp [parts, List.map_map, Function.comp_def, List.intercalate_splitOn]

theorem parts_empty_string (h : parts s = [""]) : s = "" := by
  have hs := parts_reassemble s
  rw [h] at hs
  simpa using hs.symm

def languageTag (ss : List String) : Prop :=
  langtag ss ∨ privateuse ss ∨ ∃ s ∈ grandfathered, ss = parts s

/-- Well-formedness is the imported grammar, not the stronger validity class. -/
def WellFormed (s : String) : Prop := languageTag (parts (asciiLower s))

theorem wellFormed_of_language (h : language (parts (asciiLower s))) : WellFormed s := by
  refine Or.inl ⟨_, [], [], [], [], [], h, Or.inl rfl, Or.inl rfl,
    ?_, ?_, Or.inl rfl, ?_⟩ <;> simp

theorem wellFormed_of_primary (h : subtag 2 3 alpha (asciiLower s)) : WellFormed s := by
  have hd : '-' ∉ (asciiLower s).toList := by
    intro hm
    have hn : ¬ alpha '-' := by unfold alpha; decide
    exact hn (h.2.2 '-' hm)
  apply wellFormed_of_language
  refine Or.inl ⟨asciiLower s, [], ?_, h, by decide, ?_⟩
  · simp [parts, List.splitOn_eq_singleton hd]
  · simp [subtags]

theorem wellFormed_grandfathered (h : asciiLower s ∈ grandfathered) : WellFormed s :=
  Or.inr (Or.inr ⟨asciiLower s, h, rfl⟩)

abbrev Tag := { s : String // WellFormed s }

def Tag.value (t : Tag) : String := asciiLower t.val

theorem wellFormed_of_lower_eq (h : asciiLower s = asciiLower t) :
    WellFormed s ↔ WellFormed t := by
  simp only [WellFormed, h]

theorem wellFormed_lower (h : WellFormed s) : WellFormed (asciiLower s) := by
  simpa only [WellFormed, asciiLower_idempotent] using h

def Tag.normalize (t : Tag) : Tag := ⟨t.value, wellFormed_lower t.property⟩

theorem Tag.normalize_value (t : Tag) : t.normalize.value = t.value :=
  asciiLower_idempotent t.val

theorem Tag.normalize_idempotent (t : Tag) : t.normalize.normalize = t.normalize :=
  Subtype.ext (asciiLower_idempotent t.val)

theorem Tag.eq_iff_spelling (s t : Tag) : s = t ↔ s.val = t.val :=
  ⟨congrArg Subtype.val, Subtype.ext⟩

theorem Tag.normalize_eq_iff_value (s t : Tag) :
    s.normalize = t.normalize ↔ s.value = t.value :=
  Tag.eq_iff_spelling _ _

theorem subtag_nonempty (hpos : 0 < lo) (h : subtag lo hi P s) : s ≠ "" := by
  intro he
  subst s
  have hl := h.1
  change lo ≤ 0 at hl
  omega

theorem language_head (h : language ss) : ∃ s rest, ss = s :: rest ∧ s ≠ "" := by
  rcases h with ⟨s, rest, he, hs, _⟩ | ⟨s, he, hs⟩ | ⟨s, he, hs⟩
  · exact ⟨s, rest, he, subtag_nonempty (by decide) hs⟩
  · exact ⟨s, [], he, subtag_nonempty (by decide) hs⟩
  · exact ⟨s, [], he, subtag_nonempty (by decide) hs⟩

theorem langtag_head (h : langtag ss) : ∃ s rest, ss = s :: rest ∧ s ≠ "" := by
  obtain ⟨l, s, r, vs, es, p, hl, _, _, _, _, _, he⟩ := h
  obtain ⟨first, rest, hf, hn⟩ := language_head hl
  refine ⟨first, rest ++ s ++ r ++ vs ++ es.flatten ++ p, ?_, hn⟩
  simp only [he, hf, List.cons_append]

theorem grandfathered_not_empty_parts :
    ∀ s ∈ grandfathered, parts s ≠ [""] := by
  intro s hs he
  have hn : ∀ s ∈ grandfathered, s ≠ "" := by simp [grandfathered]
  exact hn s hs (parts_empty_string he)

theorem wellFormed_nonempty (h : WellFormed s) : s ≠ "" := by
  intro he
  subst s
  simp only [WellFormed, parts, asciiLower, String.toList_map, String.toList_empty,
    List.map_nil, List.splitOn_nil, List.map_cons, String.ofList_nil] at h
  rcases h with h | ⟨rest, he, _⟩ | ⟨name, hn, he⟩
  · obtain ⟨first, rest, he, hf⟩ := langtag_head h
    exact hf (List.cons.inj he.symm).1
  · have hf := (List.cons.inj he).1
    exact (by decide : ("" : String) ≠ "x") hf
  · exact grandfathered_not_empty_parts name hn he.symm

end RDF11.BCP47
