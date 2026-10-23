/-
Shared notation for semantic extensions. These lemmas connect the ambient
relation notation directly to the existing typed IEXT and triple truth.
-/
import RDF11.RDFProperty

namespace RDF11.SimpleInterpretation

theorem relates_property (I : SimpleInterpretation Iri Literal U) {p x y : U}
    (h : I.Relates p x y) : I.IP p := h.choose

theorem relates_subject (I : SimpleInterpretation Iri Literal U) {p x y : U}
    (h : I.Relates p x y) : I.IR x := h.choose_spec.choose

theorem relates_object (I : SimpleInterpretation Iri Literal U) {p x y : U}
    (h : I.Relates p x y) : I.IR y := h.choose_spec.choose_spec.choose

theorem tripleTrue_iff_relates (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (t : GeneralizedTriple Iri Literal B) :
    I.TripleTrue A t ↔ ∃ p s o : U, I.denote A t.predicate = some p ∧
      I.denote A t.subject = some s ∧ I.denote A t.object = some o ∧ I.Relates p s o := by
  constructor
  · rintro ⟨p, s, o, hp, hs, ho, h⟩
    exact ⟨p.val, s.val, o.val, hp, hs, ho, p.property, s.property, o.property, h⟩
  · rintro ⟨p, s, o, hp, hs, ho, hpp, hss, hoo, h⟩
    exact ⟨⟨p, hpp⟩, ⟨s, hss⟩, ⟨o, hoo⟩, hp, hs, ho, h⟩

theorem tripleTrue_of_relates (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (t : GeneralizedTriple Iri Literal B) {p s o : U}
    (hp : I.denote A t.predicate = some p) (hs : I.denote A t.subject = some s)
    (ho : I.denote A t.object = some o) (h : I.Relates p s o) : I.TripleTrue A t :=
  (I.tripleTrue_iff_relates A t).mpr ⟨p, s, o, hp, hs, ho, h⟩

theorem iri_triple_true (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (s p o : Iri) :
    I.TripleTrue A ⟨.iri s, .iri p, .iri o⟩ ↔
      I.Relates (I.IS p).val (I.IS s).val (I.IS o).val := by
  rw [I.tripleTrue_iff_relates]
  simp [denote]

theorem named_predicate_true (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (s o : Term Iri Literal B) (p : Iri) :
    I.TripleTrue A ⟨s, .iri p, o⟩ ↔ ∃ x y,
      I.denote A s = some x ∧ I.denote A o = some y ∧ I.Relates (I.IS p).val x y := by
  rw [I.tripleTrue_iff_relates]
  simp [denote]

theorem denote_unique (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (t : Term Iri Literal B) (hx : I.denote A t = some x) (hy : I.denote A t = some y) : x = y :=
  Option.some.inj (hx.symm.trans hy)

end RDF11.SimpleInterpretation
