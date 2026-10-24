/-
Finite effective instance-subgraph search for RDF 1.1 Semantics §5.3 / Appendix A.
Substitutions are simultaneous and need not be injective. A source triple is
not consumed by a match. The term pool contains actual triple-position terms;
embedded datatype IRIs are vocabulary names but not additional match targets.
-/
import RDF11.FiniteInstances

namespace RDF11.InstanceSearch

variable {Iri Literal B : Type}
variable [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B]

def terms (G : List (GeneralizedTriple Iri Literal B)) : List (Term Iri Literal B) :=
  Enumeration.unique (G.flatMap (fun t => [t.subject, t.predicate, t.object]))

def blanks (E : List (GeneralizedTriple Iri Literal B)) : List B :=
  Enumeration.unique (E.flatMap GeneralizedTriple.blankList)

theorem mem_terms (G : List (GeneralizedTriple Iri Literal B)) (q : Term Iri Literal B) :
    q ∈ terms G ↔ ∃ t, t ∈ G ∧ (q = t.subject ∨ q = t.predicate ∨ q = t.object) := by
  simp [terms, List.mem_flatMap]

omit [DecidableEq Iri] [DecidableEq Literal] in
theorem mem_blanks (E : List (GeneralizedTriple Iri Literal B)) (b : B) :
    b ∈ blanks E ↔ GeneralizedGraph.hasBlank (Set.ofList E) b := by
  simp [blanks, List.mem_flatMap, GeneralizedTriple.mem_blankList,
    GeneralizedGraph.hasBlank, Set.ofList]

def update (μ : Substitution Iri Literal B) (b : B) (q : Term Iri Literal B) :
    Substitution Iri Literal B := fun c => if c = b then some q else μ c

omit [DecidableEq Iri] [DecidableEq Literal] in
theorem resolve_update (μ : Substitution Iri Literal B) (b c : B) (q : Term Iri Literal B) :
    (update μ b q).resolve c = if c = b then q else μ.resolve c := by
  by_cases h : c = b <;> simp [update, Substitution.resolve, h]

def assignments (pool : List (Term Iri Literal B)) (bs : List B) : List (Substitution Iri Literal B) :=
  bs.foldr (fun b previous => previous.flatMap (fun μ => pool.map (update μ b))) [fun _ => none]

omit [DecidableEq Iri] [DecidableEq Literal] in
theorem assignments_cover (pool : List (Term Iri Literal B)) (bs : List B)
    (μ : Substitution Iri Literal B) (h : ∀ b ∈ bs, μ.resolve b ∈ pool) :
    ∃ ν, ν ∈ assignments pool bs ∧ ∀ b ∈ bs, ν.resolve b = μ.resolve b := by
  induction bs with
  | nil => exact ⟨fun _ => none, by simp [assignments], by simp⟩
  | cons b bs ih =>
    obtain ⟨ν, hn, ha⟩ := ih (fun c hc => h c (List.mem_cons_of_mem b hc))
    refine ⟨update ν b (μ.resolve b), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨ν, hn, List.mem_map.mpr ⟨μ.resolve b, h b (by simp), rfl⟩⟩
    · intro c hc
      rw [resolve_update]
      split
      · rename_i he; exact congrArg μ.resolve he.symm
      · rename_i he
        exact ha c ((List.mem_cons.mp hc).resolve_left he)

omit [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B] in
theorem term_substitute_of_blank (q : Term Iri Literal B) (μ : Substitution Iri Literal B)
    (b : B) (hb : q.hasBlank b) : q.substitute μ = μ.resolve b := by
  cases q with
  | iri _ => contradiction
  | literal _ => contradiction
  | blank c => cases hb; rfl

omit [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B] in
theorem term_substitute_agrees (q : Term Iri Literal B) (μ ν : Substitution Iri Literal B)
    (h : ∀ b, q.hasBlank b → μ.resolve b = ν.resolve b) :
    q.substitute μ = q.substitute ν := by
  cases q with
  | iri _ => rfl
  | literal _ => rfl
  | blank b => exact h b rfl

omit [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B] in
theorem triple_substitute_agrees (t : GeneralizedTriple Iri Literal B)
    (μ ν : Substitution Iri Literal B)
    (h : ∀ b, t.hasBlank b → μ.resolve b = ν.resolve b) :
    t.substitute μ = t.substitute ν := by
  have hs := term_substitute_agrees t.subject μ ν (fun b hb => h b (Or.inl hb))
  have hp := term_substitute_agrees t.predicate μ ν (fun b hb => h b (Or.inr (Or.inl hb)))
  have ho := term_substitute_agrees t.object μ ν (fun b hb => h b (Or.inr (Or.inr hb)))
  simp [GeneralizedTriple.substitute, hs, hp, ho]

theorem blank_image_in_terms (G E : List (GeneralizedTriple Iri Literal B))
    (μ : Substitution Iri Literal B)
    (h : Set.subset (GeneralizedGraph.substitute μ (Set.ofList E)) (Set.ofList G))
    (b : B) (hb : b ∈ blanks E) : μ.resolve b ∈ terms G := by
  obtain ⟨t, ht, hb⟩ := (mem_blanks E b).mp hb
  apply (mem_terms G _).mpr
  refine ⟨t.substitute μ, h _ ⟨t, ht, rfl⟩, ?_⟩
  rcases hb with hs | hp | ho
  · exact Or.inl (term_substitute_of_blank t.subject μ b hs).symm
  · exact Or.inr (Or.inl (term_substitute_of_blank t.predicate μ b hp).symm)
  · exact Or.inr (Or.inr (term_substitute_of_blank t.object μ b ho).symm)

def accepts (G E : List (GeneralizedTriple Iri Literal B))
    (μ : Substitution Iri Literal B) : Bool :=
  E.all (fun t => decide (t.substitute μ ∈ G))

theorem accepts_iff (G E : List (GeneralizedTriple Iri Literal B))
    (μ : Substitution Iri Literal B) :
    accepts G E μ = true ↔ Set.subset (GeneralizedGraph.substitute μ (Set.ofList E)) (Set.ofList G) := by
  simp only [accepts, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro h _ ⟨t, ht, rfl⟩; exact h t ht
  · intro h t ht; exact h _ ⟨t, ht, rfl⟩

def candidates (G E : List (GeneralizedTriple Iri Literal B)) :
    List (Substitution Iri Literal B) := assignments (terms G) (blanks E)

theorem candidates_complete (G E : List (GeneralizedTriple Iri Literal B))
    (μ : Substitution Iri Literal B)
    (h : Set.subset (GeneralizedGraph.substitute μ (Set.ofList E)) (Set.ofList G)) :
    ∃ ν, ν ∈ candidates G E ∧ accepts G E ν = true := by
  obtain ⟨ν, hn, ha⟩ := assignments_cover (terms G) (blanks E) μ (blank_image_in_terms G E μ h)
  refine ⟨ν, hn, (accepts_iff G E ν).mpr ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have he := triple_substitute_agrees t ν μ (fun b hb => ha b ((mem_blanks E b).mpr ⟨t, ht, hb⟩))
  rw [he]
  exact h _ ⟨t, ht, rfl⟩

def search (G E : List (GeneralizedTriple Iri Literal B)) : Option (Substitution Iri Literal B) :=
  (candidates G E).find? (accepts G E)

def check (G E : List (GeneralizedTriple Iri Literal B)) : Bool := (search G E).isSome

theorem search_sound (G E : List (GeneralizedTriple Iri Literal B))
    (μ : Substitution Iri Literal B) (h : search G E = some μ) :
    Set.subset (GeneralizedGraph.substitute μ (Set.ofList E)) (Set.ofList G) :=
  (accepts_iff G E μ).mp (List.find?_some h)

theorem check_iff (G E : List (GeneralizedTriple Iri Literal B)) :
    check G E = true ↔ ∃ μ, Set.subset (GeneralizedGraph.substitute μ (Set.ofList E)) (Set.ofList G) := by
  simp only [check, search, List.find?_isSome]
  constructor
  · rintro ⟨μ, _, hm⟩; exact ⟨μ, (accepts_iff G E μ).mp hm⟩
  · rintro ⟨μ, hm⟩; exact candidates_complete G E μ hm

def decision (G E : List (GeneralizedTriple Iri Literal B)) :
    Decidable (∃ μ, Set.subset (GeneralizedGraph.substitute μ (Set.ofList E)) (Set.ofList G)) :=
  decidable_of_iff (check G E = true) (check_iff G E)

theorem check_respects_graphs (G H E F : List (GeneralizedTriple Iri Literal B))
    (hG : Set.ofList G = Set.ofList H) (hE : Set.ofList E = Set.ofList F) :
    check G E = check H F := by
  apply Bool.eq_iff_iff.mpr
  rw [check_iff, check_iff, hG, hE]

def certificate (G E : List (GeneralizedTriple Iri Literal B)) :
    Option { μ : Substitution Iri Literal B //
      Set.subset (GeneralizedGraph.substitute μ (Set.ofList E)) (Set.ofList G) } :=
  match h : search G E with
  | none => none
  | some μ => some ⟨μ, search_sound G E μ h⟩

theorem certificate_isSome (G E : List (GeneralizedTriple Iri Literal B)) :
    (certificate G E).isSome = check G E := by
  unfold certificate
  split <;> simp_all [check]

omit [DecidableEq Iri] [DecidableEq Literal] in
theorem assignments_length (pool : List (Term Iri Literal B)) (bs : List B) :
    (assignments pool bs).length = pool.length ^ bs.length := by
  induction bs with
  | nil => simp [assignments]
  | cons b bs ih =>
    simp only [assignments] at ih
    simp [assignments, List.length_flatMap, List.map_const',
      List.sum_replicate_nat, ih, Nat.pow_succ]

theorem candidates_length (G E : List (GeneralizedTriple Iri Literal B)) :
    (candidates G E).length = (terms G).length ^ (blanks E).length :=
  assignments_length _ _

theorem check_ground (G E : List (GeneralizedTriple Iri Literal B))
    (h : GeneralizedGraph.ground (Set.ofList E)) :
    check G E = E.all (fun t => decide (t ∈ G)) := by
  apply Bool.eq_iff_iff.mpr
  rw [check_iff, List.all_eq_true]
  simp only [decide_eq_true_eq, ground_substitute _ h]
  constructor
  · rintro ⟨_, hs⟩; exact hs
  · intro hs; exact ⟨fun _ => none, hs⟩

end RDF11.InstanceSearch
