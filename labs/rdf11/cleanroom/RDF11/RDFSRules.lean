/-
RDF 1.1 Semantics §9.2.1. Rule instances are triples in one common blank
domain. The soundness theorem preserves one assignment through a derivation;
it does not combine independently chosen witnesses for rule premises.
-/
import RDF11.RDFS

namespace RDF11

inductive RDFSStep (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    GeneralizedTriple Iri Literal B → Prop where
  | rdfs1 (a) : D a → RDFSStep T D v G ⟨.iri a, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .datatype)⟩
  | rdfs2 (p c s o) : G ⟨p, .iri (v.iri .domain), c⟩ → G ⟨s, p, o⟩ →
      RDFSStep T D v G ⟨s, .iri (v.iri (.rdf .rdfType)), c⟩
  | rdfs3 (p c s o) : G ⟨p, .iri (v.iri .range), c⟩ → G ⟨s, p, o⟩ →
      RDFSStep T D v G ⟨o, .iri (v.iri (.rdf .rdfType)), c⟩
  | rdfs4a (s p o) : G ⟨s, p, o⟩ →
      RDFSStep T D v G ⟨s, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .resource)⟩
  | rdfs4b (s p o) : G ⟨s, p, o⟩ →
      RDFSStep T D v G ⟨o, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .resource)⟩
  | rdfs5 (p q r) : G ⟨p, .iri (v.iri .subPropertyOf), q⟩ →
      G ⟨q, .iri (v.iri .subPropertyOf), r⟩ → RDFSStep T D v G ⟨p, .iri (v.iri .subPropertyOf), r⟩
  | rdfs6 (p) : G ⟨p, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfProperty))⟩ →
      RDFSStep T D v G ⟨p, .iri (v.iri .subPropertyOf), p⟩
  | rdfs7 (p q s o) : G ⟨p, .iri (v.iri .subPropertyOf), q⟩ → G ⟨s, p, o⟩ →
      RDFSStep T D v G ⟨s, q, o⟩
  | rdfs8 (c) : G ⟨c, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ →
      RDFSStep T D v G ⟨c, .iri (v.iri .subClassOf), .iri (v.iri .resource)⟩
  | rdfs9 (c d x) : G ⟨c, .iri (v.iri .subClassOf), d⟩ →
      G ⟨x, .iri (v.iri (.rdf .rdfType)), c⟩ → RDFSStep T D v G ⟨x, .iri (v.iri (.rdf .rdfType)), d⟩
  | rdfs10 (c) : G ⟨c, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ →
      RDFSStep T D v G ⟨c, .iri (v.iri .subClassOf), c⟩
  | rdfs11 (c d e) : G ⟨c, .iri (v.iri .subClassOf), d⟩ →
      G ⟨d, .iri (v.iri .subClassOf), e⟩ → RDFSStep T D v G ⟨c, .iri (v.iri .subClassOf), e⟩
  | rdfs12 (p) : G ⟨p, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .containerMembershipProperty)⟩ →
      RDFSStep T D v G ⟨p, .iri (v.iri .subPropertyOf), .iri (v.iri .member)⟩
  | rdfs13 (c) : G ⟨c, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .datatype)⟩ →
      RDFSStep T D v G ⟨c, .iri (v.iri .subClassOf), .iri (v.iri .literal)⟩

namespace SimpleInterpretation

theorem rdfs_step_sound (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) (A : I.Assignment B) (hG : I.GraphTrue A G)
    (step : RDFSStep T D v G t) : I.TripleTrue A t := by
  cases step with
  | rdfs1 a ha => exact I.tripleTrue_of_relates A _ rfl rfl rfl (h.datatype_typing a ha)
  | rdfs2 p c s o hd ht =>
    obtain ⟨pv, cv, hp, hc, hr⟩ := (I.named_predicate_true A p c _).mp (hG _ hd)
    obtain ⟨pv', sv, ov, hp', hs, ho, ht'⟩ := (I.tripleTrue_iff_relates A _).mp (hG _ ht)
    have he := I.denote_unique A p hp hp'; subst pv'
    exact I.tripleTrue_of_relates A _ rfl hs hc (h.domain pv cv sv ov hr ht')
  | rdfs3 p c s o hd ht =>
    obtain ⟨pv, cv, hp, hc, hr⟩ := (I.named_predicate_true A p c _).mp (hG _ hd)
    obtain ⟨pv', sv, ov, hp', hs, ho, ht'⟩ := (I.tripleTrue_iff_relates A _).mp (hG _ ht)
    have he := I.denote_unique A p hp hp'; subst pv'
    exact I.tripleTrue_of_relates A _ rfl ho hc (h.range pv cv sv ov hr ht')
  | rdfs4a s p o ht =>
    obtain ⟨pv, sv, ov, _, hs, _, hr⟩ := (I.tripleTrue_iff_relates A _).mp (hG _ ht)
    exact I.tripleTrue_of_relates A _ rfl hs rfl ((h.resource_extension sv).mpr (I.relates_subject hr))
  | rdfs4b s p o ht =>
    obtain ⟨pv, sv, ov, _, _, ho, hr⟩ := (I.tripleTrue_iff_relates A _).mp (hG _ ht)
    exact I.tripleTrue_of_relates A _ rfl ho rfl ((h.resource_extension ov).mpr (I.relates_object hr))
  | rdfs5 p q r hpq hqr =>
    obtain ⟨pv, qv, hp, hq, h₁⟩ := (I.named_predicate_true A p q _).mp (hG _ hpq)
    obtain ⟨qv', rv, hq', hr, h₂⟩ := (I.named_predicate_true A q r _).mp (hG _ hqr)
    have he := I.denote_unique A q hq hq'; subst qv'
    exact I.tripleTrue_of_relates A _ rfl hp hr (h.subproperty_transitive pv qv rv h₁ h₂)
  | rdfs6 p ht =>
    obtain ⟨pv, cv, hp, hc, hr⟩ := (I.named_predicate_true A p _ _).mp (hG _ ht)
    have he : (I.IS (v.iri (.rdf .rdfProperty))).val = cv := Option.some.inj hc
    subst cv
    exact I.tripleTrue_of_relates A _ rfl hp hp (h.subproperty_reflexive pv ((h.rdf.property pv).mpr hr))
  | rdfs7 p q s o hpq ht =>
    obtain ⟨pv, qv, hp, hq, hr⟩ := (I.named_predicate_true A p q _).mp (hG _ hpq)
    obtain ⟨pv', sv, ov, hp', hs, ho, ht'⟩ := (I.tripleTrue_iff_relates A _).mp (hG _ ht)
    have he := I.denote_unique A p hp hp'; subst pv'
    exact I.tripleTrue_of_relates A _ hq hs ho (h.subproperty_inclusion pv qv hr sv ov ht')
  | rdfs8 c ht =>
    obtain ⟨cv, kv, hc, hk, hr⟩ := (I.named_predicate_true A c _ _).mp (hG _ ht)
    have he : (I.IS (v.iri .class_)).val = kv := Option.some.inj hk
    subst kv
    exact I.tripleTrue_of_relates A _ rfl hc rfl (h.class_resource cv hr)
  | rdfs9 c d x hcd ht =>
    obtain ⟨cv, dv, hc, hd, hr⟩ := (I.named_predicate_true A c d _).mp (hG _ hcd)
    obtain ⟨xv, cv', hx, hc', ht'⟩ := (I.named_predicate_true A x c _).mp (hG _ ht)
    have he := I.denote_unique A c hc hc'; subst cv'
    exact I.tripleTrue_of_relates A _ rfl hx hd (h.subclass_inclusion cv dv hr xv ht')
  | rdfs10 c ht =>
    obtain ⟨cv, kv, hc, hk, hr⟩ := (I.named_predicate_true A c _ _).mp (hG _ ht)
    have he : (I.IS (v.iri .class_)).val = kv := Option.some.inj hk
    subst kv
    exact I.tripleTrue_of_relates A _ rfl hc hc (h.subclass_reflexive cv hr)
  | rdfs11 c d e hcd hde =>
    obtain ⟨cv, dv, hc, hd, h₁⟩ := (I.named_predicate_true A c d _).mp (hG _ hcd)
    obtain ⟨dv', ev, hd', he, h₂⟩ := (I.named_predicate_true A d e _).mp (hG _ hde)
    have hv := I.denote_unique A d hd hd'; subst dv'
    exact I.tripleTrue_of_relates A _ rfl hc he (h.subclass_transitive cv dv ev h₁ h₂)
  | rdfs12 p ht =>
    obtain ⟨pv, cv, hp, hc, hr⟩ := (I.named_predicate_true A p _ _).mp (hG _ ht)
    have he : (I.IS (v.iri .containerMembershipProperty)).val = cv := Option.some.inj hc
    subst cv
    exact I.tripleTrue_of_relates A _ rfl hp rfl (h.container_subproperty pv hr)
  | rdfs13 c ht =>
    obtain ⟨cv, dv, hc, hd, hr⟩ := (I.named_predicate_true A c _ _).mp (hG _ ht)
    have he : (I.IS (v.iri .datatype)).val = dv := Option.some.inj hd
    subst dv
    exact I.tripleTrue_of_relates A _ rfl hc rfl (h.datatype_subclass cv hr)

end SimpleInterpretation

/-- Inductive rule closure. No entailment-completeness claim is made. -/
inductive RDFSDerives (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    GeneralizedTriple Iri Literal B → Prop where
  | premise : G t → RDFSDerives T D v G t
  | rdfAxiom : v.toRDF.axioms t → RDFSDerives T D v G t
  | rdfsAxiom : v.axioms t → RDFSDerives T D v G t
  | rdfD2 : RDFSDerives T D v G t → RDFSDerives T D v G
      ⟨t.predicate, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfProperty))⟩
  | GrdfD1 (s p l) : RDFSDerives T D v G ⟨s, p, .literal l⟩ → D (T.literalSyntax.datatype l) →
      RDFSDerives T D v G ⟨.literal l, .iri (v.iri (.rdf .rdfType)), .iri (T.literalSyntax.datatype l)⟩
  | rule (H : GeneralizedGraph Iri Literal B) :
      (∀ t, H t → RDFSDerives T D v G t) → RDFSStep T D v H t → RDFSDerives T D v G t

theorem SimpleInterpretation.rdfs_derivation_sound (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) (A : I.Assignment B) (hG : I.GraphTrue A G)
    (derivation : RDFSDerives T D v G t) : I.TripleTrue A t := by
  induction derivation with
  | premise ht => exact hG _ ht
  | rdfAxiom ht => exact I.rdf_axiom_true h.rdf A _ ht
  | rdfsAxiom ht => exact I.rdfs_axiom_true h A _ ht
  | rdfD2 _ ih => exact I.rdfD2_triple h.rdf.property A _ ih
  | GrdfD1 s p l _ hd ih => exact I.GrdfD1_triple h.rdf A _ ih (Or.inr (Or.inr rfl)) hd
  | rule H _ step ih => exact I.rdfs_step_sound h A ih step

theorem rdfs_derives_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G E : GeneralizedGraph Iri Literal B)
    (h : ∀ t, E t → RDFSDerives T D v G t) : RDFSEntails.{u} T D v G E := by
  rintro U I ⟨ρ, hρ⟩ hG
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  exact (I.satisfies_iff_exists_graphTrue E).mpr
    ⟨A, fun t ht => I.rdfs_derivation_sound hρ A hA (h t ht)⟩

def RDFSUnsatisfiable.{u} (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) : Prop :=
  ¬ ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧ I.Satisfies G

theorem rdfs_disjoint_types_unsatisfiable (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (x : Term Iri Literal B) (ha : D a) (hb : D b)
    (disjoint : ∀ w, T.recognizedSpace a w → ¬ T.recognizedSpace b w)
    (derive_a : RDFSDerives T D v G ⟨x, .iri (v.iri (.rdf .rdfType)), .iri a⟩)
    (derive_b : RDFSDerives T D v G ⟨x, .iri (v.iri (.rdf .rdfType)), .iri b⟩) :
    RDFSUnsatisfiable.{u} T D v G := by
  rintro ⟨U, I, ⟨ρ, hρ⟩, hG⟩
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  obtain ⟨xa, av, hx, hav, hxa⟩ := (I.named_predicate_true A _ _ _).mp
    (I.rdfs_derivation_sound hρ A hA derive_a)
  obtain ⟨xb, bv, hx', hbv, hxb⟩ := (I.named_predicate_true A _ _ _).mp
    (I.rdfs_derivation_sound hρ A hA derive_b)
  have he := I.denote_unique A x hx hx'; subst xb
  have hea : (I.IS a).val = av := Option.some.inj hav
  have heb : (I.IS b).val = bv := Option.some.inj hbv
  subst av; subst bv
  exact I.rdf_disjoint_datatypes hρ.rdf ha hb disjoint hxa hxb

end RDF11
