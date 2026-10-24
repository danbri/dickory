/-
Appendix A: finitely many selected container names suffice. Selection counts
the names actually present in E, not all indices below its largest index.
The infinite vocabulary and printed E-only selection remain unchanged.
-/
import RDF11.ClosureTermBounds

namespace RDF11.ClosureBound

def rdfFixedSymbols : List RDFSymbol :=
  [.rdfType, .rdfProperty, .rdfSubject, .rdfPredicate, .rdfObject, .rdfFirst,
   .rdfRest, .rdfValue, .rdfNil, .rdfList, .rdfLangString, .xsdString,
   .rdfStatement, .rdfAlt, .rdfBag, .rdfSeq]

def rdfsFixedSymbols : List RDFSSymbol :=
  rdfFixedSymbols.map .rdf ++ [.domain, .range, .resource, .literal, .datatype, .class_,
    .subClassOf, .subPropertyOf, .member, .container, .containerMembershipProperty,
    .comment, .seeAlso, .isDefinedBy, .label]

theorem rdf_fixed_or_container (s : RDFSymbol) :
    s ∈ rdfFixedSymbols ∨ ∃ n, s = .container n := by
  cases s <;> simp [rdfFixedSymbols]

theorem rdfs_fixed_or_container (s : RDFSSymbol) :
    s ∈ rdfsFixedSymbols ∨ ∃ n, s = .rdf (.container n) := by
  cases s with
  | rdf r =>
    rcases rdf_fixed_or_container r with hr | ⟨n, rfl⟩
    · exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    · exact Or.inr ⟨n, rfl⟩
  | _ => simp [rdfsFixedSymbols]

theorem rdf_iri_eq (v : RDFVocabulary Iri) (a b : RDFSymbol) :
    v.iri a = v.iri b ↔ a = b := ⟨v.distinct a b, congrArg v.iri⟩

theorem rdfs_iri_eq (v : RDFSVocabulary Iri) (a b : RDFSSymbol) :
    v.iri a = v.iri b ↔ a = b := ⟨v.distinct a b, congrArg v.iri⟩

theorem rdf_axioms_onTerms (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (V : Set (Term Iri Literal B)) (hf : ∀ s ∈ rdfFixedSymbols, V (.iri (v.iri s)))
    (t : GeneralizedTriple Iri Literal B) (ha : v.axioms t)
    (hc : ∀ n, t.names datatype (.inl (v.iri (.container n))) → V (.iri (v.iri (.container n)))) :
    OnTerms V t := by
  have term (s : RDFSymbol) (hn : t.names datatype (.inl (v.iri s))) : V (.iri (v.iri s)) := by
    rcases rdf_fixed_or_container s with hs | ⟨n, rfl⟩
    · exact hf s hs
    · exact hc n hn
  rcases ha with ⟨p, _, rfl⟩ | rfl
  · exact ⟨term p (Or.inl rfl), term .rdfType (Or.inr (Or.inl rfl)),
      term .rdfProperty (Or.inr (Or.inr rfl))⟩
  · exact ⟨term .rdfNil (Or.inl rfl), term .rdfType (Or.inr (Or.inl rfl)),
      term .rdfList (Or.inr (Or.inr rfl))⟩

theorem rdfs_axioms_onTerms (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (V : Set (Term Iri Literal B)) (hf : ∀ s ∈ rdfsFixedSymbols, V (.iri (v.iri s)))
    (t : GeneralizedTriple Iri Literal B) (ha : v.axioms t)
    (hc : ∀ n, t.names datatype (.inl (v.iri (.rdf (.container n)))) →
      V (.iri (v.iri (.rdf (.container n))))) : OnTerms V t := by
  have term (s : RDFSSymbol) (hn : t.names datatype (.inl (v.iri s))) : V (.iri (v.iri s)) := by
    rcases rdfs_fixed_or_container s with hs | ⟨n, rfl⟩
    · exact hf s hs
    · exact hc n hn
  obtain ⟨s, p, o, _, rfl⟩ := ha
  exact ⟨term s (Or.inl rfl), term p (Or.inr (Or.inl rfl)), term o (Or.inr (Or.inr rfl))⟩

theorem rdf_axiom_container_unique (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (t : GeneralizedTriple Iri Literal B) (ha : v.axioms t) (m n : Nat)
    (hm : t.names datatype (.inl (v.iri (.container m))))
    (hn : t.names datatype (.inl (v.iri (.container n)))) : m = n := by
  rcases ha with ⟨p, _, rfl⟩ | rfl
  · simp only [GeneralizedTriple.names, Term.names, Sum.inl.injEq, rdf_iri_eq] at hm hn
    rcases hm with hm | hm | hm
    · rcases hn with hn | hn | hn
      · exact RDFSymbol.container.inj (hm.trans hn.symm)
      · cases hn
      · cases hn
    · cases hm
    · cases hm
  · simp [GeneralizedTriple.names, Term.names, rdf_iri_eq] at hm

theorem rdfs_fixed_not_container (s : RDFSSymbol) (hs : s ∈ rdfsFixedSymbols) (n : Nat) :
    s ≠ .rdf (.container n) := by
  intro h
  subst s
  simp [rdfsFixedSymbols, rdfFixedSymbols] at hs

theorem rdfs_fixed_triple_no_container (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (s p o : RDFSSymbol) (hs : s ∈ rdfsFixedSymbols) (hp : p ∈ rdfsFixedSymbols)
    (ho : o ∈ rdfsFixedSymbols) (n : Nat) :
    ¬ (⟨.iri (v.iri s), .iri (v.iri p), .iri (v.iri o)⟩ : GeneralizedTriple Iri Literal B).names
      datatype (.inl (v.iri (.rdf (.container n)))) := by
  intro h
  simp only [GeneralizedTriple.names, Term.names, Sum.inl.injEq, rdfs_iri_eq] at h
  exact h.elim (fun h => rdfs_fixed_not_container s hs n h.symm)
    (fun h => h.elim (fun h => rdfs_fixed_not_container p hp n h.symm)
      (fun h => rdfs_fixed_not_container o ho n h.symm))

theorem domain_symbols_fixed : ∀ x ∈ rdfsDomainAxioms,
    x.1 ∈ rdfsFixedSymbols ∧ x.2 ∈ rdfsFixedSymbols := by
  simp [rdfsDomainAxioms, rdfsFixedSymbols, rdfFixedSymbols]

theorem range_symbols_fixed : ∀ x ∈ rdfsRangeAxioms,
    x.1 ∈ rdfsFixedSymbols ∧ x.2 ∈ rdfsFixedSymbols := by
  simp [rdfsRangeAxioms, rdfsFixedSymbols, rdfFixedSymbols]

theorem hierarchy_symbols_fixed : ∀ x ∈ rdfsHierarchyAxioms,
    x.1 ∈ rdfsFixedSymbols ∧ x.2.1 ∈ rdfsFixedSymbols ∧ x.2.2 ∈ rdfsFixedSymbols := by
  simp [rdfsHierarchyAxioms, rdfsFixedSymbols, rdfFixedSymbols]

theorem rdfs_axiom_container_unique (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (t : GeneralizedTriple Iri Literal B) (ha : v.axioms t) (m n : Nat)
    (hm : t.names datatype (.inl (v.iri (.rdf (.container m)))))
    (hn : t.names datatype (.inl (v.iri (.rdf (.container n))))) : m = n := by
  obtain ⟨s, p, o, ha, rfl⟩ := ha
  rcases ha with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha | ⟨k, rfl, ha⟩
  · have hf := domain_symbols_fixed (s, o) ha
    exact False.elim (rdfs_fixed_triple_no_container datatype v s .domain o hf.1
      (by simp [rdfsFixedSymbols]) hf.2 m hm)
  · have hf := range_symbols_fixed (s, o) ha
    exact False.elim (rdfs_fixed_triple_no_container datatype v s .range o hf.1
      (by simp [rdfsFixedSymbols]) hf.2 m hm)
  · have hf := hierarchy_symbols_fixed (s, p, o) ha
    exact False.elim (rdfs_fixed_triple_no_container datatype v s p o hf.1 hf.2.1 hf.2.2 m hm)
  · rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [GeneralizedTriple.names, Term.names, rdfs_iri_eq] at hm hn <;> omega

theorem seed_onTerms (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (V : Set (Term Iri Literal B₁)) (hG : Set.subset G (OnTerms V))
    (ha : ∀ t, axioms t → (∀ n, t.names datatype (.inl (container n)) → V (.iri (container n))) → OnTerms V t)
    (hu : ∀ t, axioms t → ∀ m n, t.names datatype (.inl (container m)) →
      t.names datatype (.inl (container n)) → m = n)
    (hE : ∀ n, E.vocabulary datatype (.inl (container n)) → V (.iri (container n)))
    (h0 : V (.iri (container 0))) :
    Set.subset (AxiomSeed datatype container axioms G E) (OnTerms V) := by
  intro t ht
  rcases ht with hg | ⟨ha', hn⟩ | ⟨n, he, ha', hn⟩ | ⟨_, ha', hn⟩
  · exact hG t hg
  · exact ha t ha' (fun n h => False.elim (hn ⟨n, h⟩))
  · apply ha t ha'
    intro k hk
    have heq := hu t ha' k n hk hn
    exact heq.symm ▸ hE n he
  · apply ha t ha'
    intro k hk
    have heq := hu t ha' k 0 hk hn
    exact heq.symm ▸ h0

theorem finite_preimage_injective {α : Type u} {β : Type v} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (S : Set β) (e : Enumeration S) :
    Nonempty (Enumeration (fun a => S (f a))) := by
  classical
  let pick (b : β) : Option α := if h : ∃ a, f a = b then some h.choose else none
  have hit (a : α) : pick (f a) = some a := by
    dsimp [pick]
    split
    · rename_i h
      exact congrArg some (hf _ a h.choose_spec)
    · rename_i h
      exact False.elim (h ⟨a, rfl⟩)
  have origin (b : β) (a : α) (h : pick b = some a) : f a = b := by
    dsimp [pick] at h
    split at h
    · rename_i hex
      exact Option.some.inj h ▸ hex.choose_spec
    · cases h
  let result := Enumeration.fromList (e.triples.filterMap pick)
  refine ⟨⟨result.triples, result.nodup, ?_⟩⟩
  intro a
  rw [result.membership]
  change a ∈ e.triples.filterMap pick ↔ S (f a)
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, hp⟩
    rw [origin b a hp]
    exact (e.membership b).mp hb
  · intro ha
    exact ⟨f a, (e.membership _).mpr ha, hit a⟩

theorem selected_indices_finite (datatype : Literal → Iri) (container : Nat → Iri)
    (hc : ∀ m n, container m = container n → m = n)
    (E : GeneralizedGraph Iri Literal B) (he : FiniteGraph E) :
    Nonempty (Enumeration (fun n => E.vocabulary datatype (.inl (container n)))) := by
  obtain ⟨e⟩ := finite_vocabulary_of_finite_graph datatype E he
  exact finite_preimage_injective (fun n => .inl (container n))
    (fun m n h => hc m n (Sum.inl.inj h)) _ e

end RDF11.ClosureBound
