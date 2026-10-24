/-
Proof-support relation for Appendix A's blank-predicate example.
This is NOT an RDFS interpretation. It is closed under ordinary-conclusion
rule applications and includes every axiom, but forbids the needed conclusion.
The generalized rdfs7 rule deliberately fails to preserve this relation.
-/
import RDF11.OrdinaryRuleRuns

namespace RDF11.OrdinaryRuleScope

inductive Tag where
  | top | typing | domain | range | subproperty | subclass | member
  | propertyA | classC | subjectD | objectE | hidden | invalid
  deriving DecidableEq

def holds (s p o : Tag) : Prop :=
  match p with
  | .typing => s ≠ .invalid ∧ o = .top
  | .domain => s ≠ .invalid ∧ (o = .top ∨ (s = .hidden ∧ o = .classC))
  | .range => s ≠ .invalid ∧ o = .top
  | .subproperty => s ≠ .invalid ∧ o ≠ .invalid ∧
      (s = o ∨ o = .member ∨ (s = .propertyA ∧ o = .hidden))
  | .subclass => s ≠ .invalid ∧ o ≠ .invalid ∧ (o = .top ∨ s = o)
  | .member => s ≠ .invalid ∧ o ≠ .invalid
  | .propertyA => s = .subjectD ∧ o = .objectE
  | _ => False

theorem subject_valid {s p o : Tag} (h : holds s p o) : s ≠ .invalid := by
  cases p <;> cases s <;> simp_all [holds]

theorem object_valid {s p o : Tag} (h : holds s p o) : o ≠ .invalid := by
  cases p <;> cases o <;> simp_all [holds]

theorem predicate_valid {s p o : Tag} (h : holds s p o) : p ≠ .invalid := by
  cases p <;> simp_all [holds]

theorem type_top {s : Tag} (h : s ≠ .invalid) : holds s .typing .top := ⟨h, rfl⟩

theorem domain_closed {p c s o : Tag} (hd : holds p .domain c) (ht : holds s p o) :
    holds s .typing c := by
  rcases hd.2 with rfl | ⟨rfl, _⟩
  · exact type_top (subject_valid ht)
  · exact False.elim ht

theorem range_closed {p c s o : Tag} (hd : holds p .range c) (ht : holds s p o) :
    holds o .typing c := by
  rcases hd with ⟨_, rfl⟩
  exact type_top (object_valid ht)

theorem subproperty_trans {p q r : Tag} (hpq : holds p .subproperty q)
    (hqr : holds q .subproperty r) : holds p .subproperty r := by
  refine ⟨hpq.1, hqr.2.1, ?_⟩
  rcases hpq.2.2 with rfl | rfl | ⟨rfl, rfl⟩
  · exact hqr.2.2
  · rcases hqr.2.2 with rfl | hr | ⟨h, _⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl hr)
    · cases h
  · rcases hqr.2.2 with rfl | hr | ⟨h, _⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl hr)
    · cases h

theorem subproperty_refl {p : Tag} (h : p ≠ .invalid) : holds p .subproperty p :=
  ⟨h, h, Or.inl rfl⟩

/-- The omitted blank-predicate case is exactly the extra hypothesis. -/
theorem subproperty_use {p q s o : Tag} (hpq : holds p .subproperty q)
    (ht : holds s p o) (hq : q ≠ .hidden) : holds s q o := by
  rcases hpq.2.2 with rfl | rfl | ⟨_, rfl⟩
  · exact ht
  · exact ⟨subject_valid ht, object_valid ht⟩
  · exact False.elim (hq rfl)

theorem subclass_top {c : Tag} (hc : c ≠ .invalid) : holds c .subclass .top :=
  ⟨hc, by decide, Or.inl rfl⟩

theorem subclass_refl {c : Tag} (hc : c ≠ .invalid) : holds c .subclass c :=
  ⟨hc, hc, Or.inr rfl⟩

theorem subclass_use {c d x : Tag} (hcd : holds c .subclass d)
    (hx : holds x .typing c) : holds x .typing d := by
  rcases hcd.2.2 with rfl | rfl
  · exact type_top hx.1
  · exact hx

theorem subclass_trans {c d e : Tag} (hcd : holds c .subclass d)
    (hde : holds d .subclass e) : holds c .subclass e := by
  refine ⟨hcd.1, hde.2.1, ?_⟩
  rcases hde.2.2 with rfl | rfl
  · exact Or.inl rfl
  · exact hcd.2.2

theorem to_member {p : Tag} (hp : p ≠ .invalid) : holds p .subproperty .member :=
  ⟨hp, by decide, Or.inr (Or.inl rfl)⟩

inductive UserName where
  | a | c | d | e
  deriving DecidableEq

abbrev Iri := Sum RDFSSymbol UserName

def vocabulary : RDFSVocabulary Iri where
  iri := Sum.inl
  distinct := fun _ _ h => Sum.inl.inj h

def schemaTag : RDFSSymbol → Tag
  | .rdf .rdfType => .typing
  | .domain => .domain
  | .range => .range
  | .subPropertyOf => .subproperty
  | .subClassOf => .subclass
  | .member => .member
  | _ => .top

def iriTag : Iri → Tag
  | .inl s => schemaTag s
  | .inr .a => .propertyA
  | .inr .c => .classC
  | .inr .d => .subjectD
  | .inr .e => .objectE

def termTag : Term Iri Literal B → Tag
  | .iri a => iriTag a
  | .blank _ => .hidden
  | .literal _ => .invalid

def Supported (t : GeneralizedTriple Iri Literal B) : Prop :=
  holds (termTag t.subject) (termTag t.predicate) (termTag t.object)

theorem schema_valid (s : RDFSSymbol) : schemaTag s ≠ .invalid := by
  cases s with
  | rdf r => cases r <;> simp [schemaTag]
  | _ => simp [schemaTag]

theorem iri_not_hidden (a : Iri) : iriTag a ≠ .hidden := by
  cases a with
  | inl s => cases s with
    | rdf r => cases r <;> simp [iriTag, schemaTag]
    | _ => simp [iriTag, schemaTag]
  | inr user => cases user <;> simp [iriTag]

theorem ordinary_predicate_not_hidden {t : GeneralizedTriple Iri Literal B}
    (h : t.Ordinary) : termTag t.predicate ≠ .hidden := by
  obtain ⟨q, rfl⟩ := h
  exact iri_not_hidden q.predicate

theorem rdf_step_closed (T : DatatypeTheory Iri Literal Value)
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H Supported)
    (h : RDFStep T vocabulary.toRDF.baseDatatypes vocabulary.toRDF H t) : Supported t := by
  cases h with
  | rdfD2 t ht => exact type_top (predicate_valid (hH t ht))
  | GrdfD1 s p l ht _ => exact False.elim ((object_valid (hH _ ht)) rfl)

theorem rdfs_step_closed (T : DatatypeTheory Iri Literal Value)
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H Supported)
    (h : RDFSStep T vocabulary.toRDF.baseDatatypes vocabulary H t)
    (ho : t.Ordinary) : Supported t := by
  cases h with
  | rdfs1 a ha =>
    rcases ha with rfl | rfl
    · exact type_top (schema_valid (.rdf .rdfLangString))
    · exact type_top (schema_valid (.rdf .xsdString))
  | rdfs2 p c s o hd ht => exact domain_closed (hH _ hd) (hH _ ht)
  | rdfs3 p c s o hd ht => exact range_closed (hH _ hd) (hH _ ht)
  | rdfs4a s p o ht =>
    have hh := hH _ ht
    exact type_top (subject_valid hh)
  | rdfs4b s p o ht => exact type_top (object_valid (hH _ ht))
  | rdfs5 p q r hpq hqr =>
    have h1 := hH _ hpq
    have h2 := hH _ hqr
    exact subproperty_trans h1 h2
  | rdfs6 p hp =>
    have hh := hH _ hp
    exact subproperty_refl (subject_valid hh)
  | rdfs7 p q s o hpq ht =>
    exact subproperty_use (hH _ hpq) (hH _ ht) (ordinary_predicate_not_hidden ho)
  | rdfs8 c hc =>
    have hh := hH _ hc
    exact subclass_top (subject_valid hh)
  | rdfs9 c d x hcd hx => exact subclass_use (hH _ hcd) (hH _ hx)
  | rdfs10 c hc =>
    have hh := hH _ hc
    exact subclass_refl (subject_valid hh)
  | rdfs11 c d e hcd hde =>
    have h1 := hH _ hcd
    have h2 := hH _ hde
    exact subclass_trans h1 h2
  | rdfs12 p hp =>
    have hh := hH _ hp
    exact to_member (subject_valid hh)
  | rdfs13 c hc =>
    have hh := hH _ hc
    exact subclass_top (subject_valid hh)

theorem step_closed (T : DatatypeTheory Iri Literal Value)
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H Supported)
    (h : RDFSGeneralizedStep T vocabulary.toRDF.baseDatatypes vocabulary H t)
    (ho : t.Ordinary) : Supported t :=
  h.elim (rdf_step_closed T H hH) (fun hs => rdfs_step_closed T H hH hs ho)

theorem supported_no_literal {t : GeneralizedTriple Iri Literal B}
    (h : Supported t) (l : Literal) : ¬ t.hasLiteral l := by
  have term_no (q : Term Iri Literal B) (hq : termTag q ≠ .invalid) : ¬ q.hasLiteral l := by
    cases q <;> simp_all [Term.hasLiteral, termTag]
  intro hl
  rcases hl with hl | hl | hl
  · exact term_no t.subject (subject_valid h) hl
  · exact term_no t.predicate (predicate_valid h) hl
  · exact term_no t.object (object_valid h) hl

theorem rdf_axioms_supported :
    Set.subset (vocabulary.toRDF.axioms : GeneralizedGraph Iri Literal B) Supported := by
  rintro t (⟨p, _, rfl⟩ | rfl)
  · exact type_top (schema_valid (.rdf p))
  · exact type_top (schema_valid (.rdf .rdfNil))

theorem domain_axioms_supported : ∀ pair ∈ rdfsDomainAxioms,
    holds (schemaTag pair.1) .domain (schemaTag pair.2) := by
  simp [rdfsDomainAxioms, schemaTag, holds]

theorem range_axioms_supported : ∀ pair ∈ rdfsRangeAxioms,
    holds (schemaTag pair.1) .range (schemaTag pair.2) := by
  simp [rdfsRangeAxioms, schemaTag, holds]

theorem hierarchy_axioms_supported : ∀ t ∈ rdfsHierarchyAxioms,
    holds (schemaTag t.1) (schemaTag t.2.1) (schemaTag t.2.2) := by
  simp [rdfsHierarchyAxioms, schemaTag, holds]

theorem rdfs_axioms_supported :
    Set.subset (vocabulary.axioms : GeneralizedGraph Iri Literal B) Supported := by
  rintro t ⟨s, p, o, ha, rfl⟩
  rcases ha with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha | ⟨n, rfl, ha⟩
  · exact domain_axioms_supported _ ha
  · exact range_axioms_supported _ ha
  · exact hierarchy_axioms_supported _ ha
  · rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact type_top (schema_valid (.rdf (.container n)))
    · exact ⟨schema_valid (.rdf (.container n)), Or.inl rfl⟩
    · exact ⟨schema_valid (.rdf (.container n)), rfl⟩

theorem run_supported (T : DatatypeTheory Iri Literal Value)
    {seed H : GeneralizedGraph Iri Literal B}
    (hs : Set.subset seed (Supported : GeneralizedGraph Iri Literal B))
    (run : OrdinaryRun T vocabulary.toRDF.baseDatatypes vocabulary.toRDF
      (RDFSGeneralizedStep T vocabulary.toRDF.baseDatatypes vocabulary) seed H) :
    Set.subset H Supported := by
  induction run with
  | start => exact hs
  | next _ ht ih =>
    cases ht with
    | rule t ht ho =>
      rintro q (hq | rfl)
      · exact ih q hq
      · exact step_closed T _ ih ht ho
    | rdfD1 s p l b ht _ _ _ => exact False.elim ((object_valid (ih _ ht)) rfl)

end RDF11.OrdinaryRuleScope
