/-
RDF 1.1 Semantics §8, rdfsemcond1, and informative rdfD2.
This is ONE RDF semantic condition over the existing SimpleInterpretation,
not the full RDF/D-interpretation definition. The condition itself forces
IP ⊆ IR; the simple interpretation type is deliberately unchanged.
-/
import RDF11.Instances

namespace RDF11
namespace SimpleInterpretation

/-- Ambient-valued notation for membership in the existing typed IEXT relation. -/
def Relates (I : SimpleInterpretation Iri Literal U) (p x y : U) : Prop :=
  ∃ hp : I.IP p, ∃ hx : I.IR x, ∃ hy : I.IR y, I.IEXT ⟨p, hp⟩ (⟨x, hx⟩, ⟨y, hy⟩)

def RDFPropertyCondition (I : SimpleInterpretation Iri Literal U) (rdfType rdfProperty : Iri) : Prop :=
  ∀ x, I.IP x ↔ I.Relates (I.IS rdfType).val x (I.IS rdfProperty).val

theorem rdf_properties_are_resources (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFPropertyCondition rdfType rdfProperty) : Set.subset I.IP I.IR := by
  intro x hx
  obtain ⟨_, hr, _, _⟩ := (h x).mp hx
  exact hr

theorem rdfD2_triple (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFPropertyCondition rdfType rdfProperty) (A : I.Assignment B)
    (t : GeneralizedTriple Iri Literal B) (ht : I.TripleTrue A t) :
    I.TripleTrue A ⟨t.predicate, .iri rdfType, .iri rdfProperty⟩ := by
  obtain ⟨p, _, _, hp, _, _, _⟩ := ht
  obtain ⟨htype, hpIR, hpropertyIR, hext⟩ := (h p.val).mp p.property
  exact ⟨⟨(I.IS rdfType).val, htype⟩, ⟨p.val, hpIR⟩,
    ⟨(I.IS rdfProperty).val, hpropertyIR⟩, rfl, hp, rfl, hext⟩

/-- The missing resource condition is explicit; ordinary triple pullback needed no such premise. -/
theorem generalized_triple_pullback (I : SimpleInterpretation Iri Literal U)
    (hIR : Set.subset I.IP I.IR) (A : I.Assignment B) (μ : Substitution Iri Literal B)
    (t : GeneralizedTriple Iri Literal B) (h : I.TripleTrue A (t.substitute μ)) :
    I.TripleTrue (I.pullback A μ) t := by
  obtain ⟨p, s, o, hp, hs, ho, hext⟩ := h
  exact ⟨p, s, o, I.denote_pullback A μ t.predicate ⟨p.val, hIR p.val p.property⟩ hp,
    I.denote_pullback A μ t.subject s hs, I.denote_pullback A μ t.object o ho, hext⟩

end SimpleInterpretation

def propertyTypingImage (rdfType rdfProperty : Iri) (G : GeneralizedGraph Iri Literal B) :
    GeneralizedGraph Iri Literal B :=
  Set.image (fun t => ⟨t.predicate, .iri rdfType, .iri rdfProperty⟩) G

theorem rdfD2_entailment (rdfType rdfProperty : Iri) (G : GeneralizedGraph Iri Literal B) :
    EntailsUnder.{u} (fun _ I => I.RDFPropertyCondition rdfType rdfProperty)
      G (propertyTypingImage rdfType rdfProperty G) := by
  intro U I hC hG
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨A, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact I.rdfD2_triple hC A t (hA t ht)

/-- A generalized-instance theorem for interpretations satisfying rdfsemcond1. -/
theorem rdf_condition_substitution_entails (rdfType rdfProperty : Iri)
    (G : GeneralizedGraph Iri Literal B) (μ : Substitution Iri Literal B) :
    EntailsUnder.{u} (fun _ I => I.RDFPropertyCondition rdfType rdfProperty) (G.substitute μ) G := by
  intro U I hC h
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp h
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨I.pullback A μ, ?_⟩
  intro t ht
  exact I.generalized_triple_pullback (I.rdf_properties_are_resources hC) A μ t (hA _ ⟨t, ht, rfl⟩)

end RDF11
