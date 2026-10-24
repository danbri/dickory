/-
Appendix A proof support: a finite set of terms bounds generalized triples.
Datatype IRIs embedded in literals are included explicitly. The enumeration
of an arbitrary closed subset is noncomputable and is not a runtime bound.
-/
import RDF11.EntailmentClosure
import RDF11.FiniteSimpleModels

namespace RDF11.ClosureBound

def expanded (datatype : Literal → Iri) : Term Iri Literal B → List (Term Iri Literal B)
  | .literal l => [.literal l, .iri (datatype l)]
  | t => [t]

theorem mem_expanded (datatype : Literal → Iri) (t : Term Iri Literal B) :
    t ∈ expanded datatype t := by cases t <;> simp [expanded]

theorem expanded_literal (datatype : Literal → Iri) (t : Term Iri Literal B)
    (h : .literal l ∈ expanded datatype t) : .iri (datatype l) ∈ expanded datatype t := by
  cases t <;> simp_all [expanded]

def tripleTerms (datatype : Literal → Iri) (t : GeneralizedTriple Iri Literal B) :
    List (Term Iri Literal B) :=
  expanded datatype t.subject ++ expanded datatype t.predicate ++ expanded datatype t.object

def OnTerms (V : Set (Term Iri Literal B)) (t : GeneralizedTriple Iri Literal B) : Prop :=
  V t.subject ∧ V t.predicate ∧ V t.object

def termPool (datatype : Literal → Iri) (fixed : List Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) : List (Term Iri Literal B) :=
  fixed.map Term.iri ++ triples.flatMap (tripleTerms datatype)

theorem pool_fixed (datatype : Literal → Iri) (fixed : List Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (h : a ∈ fixed) :
    .iri a ∈ termPool datatype fixed triples :=
  List.mem_append_left _ (List.mem_map.mpr ⟨a, h, rfl⟩)

theorem pool_triple (datatype : Literal → Iri) (fixed : List Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (h : t ∈ triples) :
    OnTerms (Set.ofList (termPool datatype fixed triples)) t := by
  have add (x : Term Iri Literal B) (hx : x ∈ tripleTerms datatype t) :
      x ∈ termPool datatype fixed triples :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, h, hx⟩)
  exact ⟨add _ (by simp [tripleTerms, mem_expanded]),
    add _ (by simp [tripleTerms, mem_expanded]), add _ (by simp [tripleTerms, mem_expanded])⟩

theorem pool_literal (datatype : Literal → Iri) (fixed : List Iri)
    (triples : List (GeneralizedTriple Iri Literal B))
    (h : .literal l ∈ termPool datatype fixed triples) :
    .iri (datatype l) ∈ termPool datatype fixed triples := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨_, _, he⟩ := List.mem_map.mp h
    cases he
  · obtain ⟨t, ht, hl⟩ := List.mem_flatMap.mp h
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨t, ht, ?_⟩
    simp only [tripleTerms, List.mem_append, or_assoc] at hl ⊢
    exact hl.elim (fun h => Or.inl (expanded_literal datatype _ h))
      (fun h => h.elim (fun h => Or.inr (Or.inl (expanded_literal datatype _ h)))
        (fun h => Or.inr (Or.inr (expanded_literal datatype _ h))))

def cube (xs : List (Term Iri Literal B)) : List (GeneralizedTriple Iri Literal B) :=
  xs.flatMap (fun s => xs.flatMap (fun p => xs.map (fun o => ⟨s, p, o⟩)))

theorem mem_cube (xs : List (Term Iri Literal B)) (t : GeneralizedTriple Iri Literal B) :
    t ∈ cube xs ↔ OnTerms (Set.ofList xs) t := by
  obtain ⟨s, p, o⟩ := t
  simp only [cube, List.mem_flatMap, List.mem_map, GeneralizedTriple.mk.injEq,
    OnTerms, Set.ofList]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, rfl, rfl⟩
    exact ⟨ha, hb, hc⟩
  · rintro ⟨hs, hp, ho⟩
    exact ⟨s, hs, p, hp, o, ho, rfl, rfl, rfl⟩

theorem length_flatMap_constant (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem cube_length (xs : List (Term Iri Literal B)) : (cube xs).length = xs.length ^ 3 := by
  have hi (s : Term Iri Literal B) :
      (xs.flatMap (fun p => xs.map (fun o => (⟨s, p, o⟩ : GeneralizedTriple Iri Literal B)))).length =
        xs.length * xs.length :=
    length_flatMap_constant xs _ _ (by intro p _; simp)
  have ho := length_flatMap_constant xs _ _ (fun s _ => hi s)
  simpa [cube, Nat.pow_succ, Nat.mul_assoc] using ho

theorem graph_bound (V : Set (Term Iri Literal B)) (e : Enumeration V)
    (G : GeneralizedGraph Iri Literal B) (hG : Set.subset G (OnTerms V)) :
    ∃ g : Enumeration G, g.triples.length ≤ e.triples.length ^ 3 := by
  classical
  let c := Enumeration.fromList (cube e.triples)
  have hc : Set.subset G (Set.ofList (cube e.triples)) := by
    intro t ht
    have h := hG t ht
    exact (mem_cube e.triples t).mpr
      ⟨(e.membership _).mpr h.1, (e.membership _).mpr h.2.1, (e.membership _).mpr h.2.2⟩
  refine ⟨c.subset G hc, Nat.le_trans (c.subset_length G hc) ?_⟩
  exact Nat.le_trans (Enumeration.fromList_length _) (Nat.le_of_eq (cube_length e.triples))

/-- Count only distinct newly inserted facts. Unsuccessful or repeated rule
applications and their computational costs are not counted. -/
theorem insertion_bound {α : Type u} (S C : Set α) (s : Enumeration S) (c : Enumeration C)
    (hSC : Set.subset S C) (xs : List α) (hx : xs.Nodup)
    (hC : ∀ x ∈ xs, C x) (hnew : ∀ x ∈ xs, ¬ S x) (n : Nat)
    (hc : c.triples.length ≤ n) : xs.length ≤ n - s.triples.length := by
  have hn : (s.triples ++ xs).Nodup := by
    apply List.pairwise_append.mpr
    refine ⟨s.nodup, hx, ?_⟩
    intro a ha b hb he
    exact hnew b hb (he ▸ (s.membership a).mp ha)
  have hs : s.triples ++ xs ⊆ c.triples := by
    intro a ha
    apply (c.membership a).mpr
    rcases List.mem_append.mp ha with h | h
    · exact hSC a ((s.membership a).mp h)
    · exact hC a h
  have hl := hn.length_le_of_subset hs
  simp only [List.length_append] at hl
  omega

theorem rdf_step_onTerms (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (V : Set (Term Iri Literal B))
    (ht : V (.iri (v.iri .rdfType))) (hp : V (.iri (v.iri .rdfProperty)))
    (hl : ∀ l, V (.literal l) → V (.iri (T.literalSyntax.datatype l)))
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H (OnTerms V))
    (h : RDFStep T D v H t) : OnTerms V t := by
  cases h with
  | rdfD2 t h => exact ⟨(hH _ h).2.1, ht, hp⟩
  | GrdfD1 s p l h _ => exact ⟨(hH _ h).2.2, ht, hl l (hH _ h).2.2⟩

def rdfsRuleNames (v : RDFSVocabulary Iri) : List Iri :=
  [.rdf .rdfType, .resource, .datatype, .subPropertyOf, .subClassOf, .member, .literal].map v.iri

theorem rdfs_step_onTerms (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (V : Set (Term Iri Literal B))
    (hv : ∀ a ∈ rdfsRuleNames v, V (.iri a)) (hd : ∀ a, D a → V (.iri a))
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H (OnTerms V))
    (h : RDFSStep T D v H t) : OnTerms V t := by
  have htype := hv (v.iri (.rdf .rdfType)) (by simp [rdfsRuleNames])
  have hresource := hv (v.iri .resource) (by simp [rdfsRuleNames])
  have hdatatype := hv (v.iri .datatype) (by simp [rdfsRuleNames])
  have hsubp := hv (v.iri .subPropertyOf) (by simp [rdfsRuleNames])
  have hsubc := hv (v.iri .subClassOf) (by simp [rdfsRuleNames])
  have hmember := hv (v.iri .member) (by simp [rdfsRuleNames])
  have hliteral := hv (v.iri .literal) (by simp [rdfsRuleNames])
  cases h with
  | rdfs1 a ha => exact ⟨hd a ha, htype, hdatatype⟩
  | rdfs2 p c s o hx hy => exact ⟨(hH _ hy).1, htype, (hH _ hx).2.2⟩
  | rdfs3 p c s o hx hy => exact ⟨(hH _ hy).2.2, htype, (hH _ hx).2.2⟩
  | rdfs4a s p o hx => exact ⟨(hH _ hx).1, htype, hresource⟩
  | rdfs4b s p o hx => exact ⟨(hH _ hx).2.2, htype, hresource⟩
  | rdfs5 p q r hx hy => exact ⟨(hH _ hx).1, hsubp, (hH _ hy).2.2⟩
  | rdfs6 p hx => exact ⟨(hH _ hx).1, hsubp, (hH _ hx).1⟩
  | rdfs7 p q s o hx hy => exact ⟨(hH _ hy).1, (hH _ hx).2.2, (hH _ hy).2.2⟩
  | rdfs8 c hx => exact ⟨(hH _ hx).1, hsubc, hresource⟩
  | rdfs9 c d x hx hy => exact ⟨(hH _ hy).1, htype, (hH _ hx).2.2⟩
  | rdfs10 c hx => exact ⟨(hH _ hx).1, hsubc, (hH _ hx).1⟩
  | rdfs11 c d e hx hy => exact ⟨(hH _ hx).1, hsubc, (hH _ hy).2.2⟩
  | rdfs12 p hx => exact ⟨(hH _ hx).1, hsubp, hmember⟩
  | rdfs13 c hx => exact ⟨(hH _ hx).1, hsubc, hliteral⟩

end RDF11.ClosureBound
