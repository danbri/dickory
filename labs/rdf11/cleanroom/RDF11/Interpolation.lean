/-
RDF 1.1 Semantics §5.3 and Appendix C: the Herbrand-style interpretation
connects model-theoretic entailment to the existing syntactic instance relation.
An extra carrier element keeps IR nonempty even when every term domain is empty.
It is not a graph member and cannot occur in an IEXT witness.
-/
import RDF11.Instances

namespace RDF11
namespace Herbrand

abbrev Carrier.{u} (Iri Literal B : Type) := ULift.{u} (Option (Term Iri Literal B))

def encode (q : Term Iri Literal B) : Carrier.{u} Iri Literal B := ⟨some q⟩

def interpretation (G : GeneralizedGraph Iri Literal B) :
    SimpleInterpretation Iri Literal (Carrier.{u} Iri Literal B) where
  IR := fun _ => True
  IR_nonempty := ⟨⟨none⟩, True.intro⟩
  IP := fun _ => True
  IEXT := fun p pair => ∃ t, G t ∧ p.val = encode t.predicate ∧
    pair.1.val = encode t.subject ∧ pair.2.val = encode t.object
  IS := fun i => ⟨encode (.iri i), Or.inl True.intro⟩
  IL := fun l => some ⟨encode (.literal l), True.intro⟩

def assignment (G : GeneralizedGraph Iri Literal B) : (interpretation.{u} G).Assignment B :=
  fun b => some ⟨encode (.blank b), True.intro⟩

theorem denote_assignment (G : GeneralizedGraph Iri Literal B) (q : Term Iri Literal B) :
    (interpretation.{u} G).denote (assignment G) q = some (encode q) := by
  cases q <;> rfl

theorem satisfies (G : GeneralizedGraph Iri Literal B) : (interpretation.{u} G).Satisfies G := by
  apply ((interpretation G).satisfies_iff_exists_graphTrue G).mpr
  refine ⟨assignment G, ?_⟩
  intro t ht
  exact ⟨⟨encode t.predicate, True.intro⟩, ⟨encode t.subject, True.intro⟩,
    ⟨encode t.object, True.intro⟩, denote_assignment G t.predicate,
    denote_assignment G t.subject, denote_assignment G t.object, t, ht, rfl, rfl, rfl⟩

/-- Decode the target witness into the already defined partial term substitution. -/
def substitution (G : GeneralizedGraph Iri Literal B)
    (A : (interpretation.{u} G).Assignment B) : Substitution Iri Literal B :=
  fun b => (A b).bind (fun r => r.val.down)

theorem decode_denotation (G : GeneralizedGraph Iri Literal B)
    (A : (interpretation.{u} G).Assignment B) (q v : Term Iri Literal B)
    (h : (interpretation G).denote A q = some (encode v)) :
    q.substitute (substitution G A) = v := by
  cases q with
  | iri i =>
    exact Option.some.inj (congrArg ULift.down (Option.some.inj h))
  | literal l =>
    exact Option.some.inj (congrArg ULift.down (Option.some.inj h))
  | blank b =>
    cases hb : A b with
    | none => simp [SimpleInterpretation.denote, hb] at h
    | some r =>
      have he : r.val = encode v := by
        exact Option.some.inj (by simpa [SimpleInterpretation.denote, hb] using h)
      simp [Term.substitute, Substitution.resolve, substitution, hb, he, encode]

theorem true_triple_decodes (G : GeneralizedGraph Iri Literal B)
    (A : (interpretation.{u} G).Assignment B) (t : GeneralizedTriple Iri Literal B)
    (h : (interpretation G).TripleTrue A t) : G (t.substitute (substitution G A)) := by
  obtain ⟨p, s, o, hp, hs, ho, v, hv, ep, es, eo⟩ := h
  have hpred := decode_denotation G A t.predicate v.predicate (hp.trans (congrArg some ep))
  have hsubj := decode_denotation G A t.subject v.subject (hs.trans (congrArg some es))
  have hobj := decode_denotation G A t.object v.object (ho.trans (congrArg some eo))
  have he : t.substitute (substitution G A) = v := by
    simp [GeneralizedTriple.substitute, hpred, hsubj, hobj]
  exact he.symm ▸ hv

end Herbrand

/-- Necessary direction is valid even with generalized syntax. -/
theorem entailment_has_instance_subgraph {G E : GeneralizedGraph Iri Literal B}
    (h : SimplyEntails.{u} G E) : ∃ μ, Set.subset (E.substitute μ) G := by
  have hE := h (Herbrand.Carrier.{u} Iri Literal B) (Herbrand.interpretation G) (Herbrand.satisfies G)
  obtain ⟨A, hA⟩ := ((Herbrand.interpretation G).satisfies_iff_exists_graphTrue E).mp hE
  refine ⟨Herbrand.substitution G A, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact Herbrand.true_triple_decodes G A t (hA t ht)

/-- Full equivalence for ordinary conclusions; the premise may be generalized. -/
theorem ordinary_interpolation (G : GeneralizedGraph Iri Literal B) (E : Graph Iri Literal B) :
    SimplyEntails.{u} G E.generalize ↔ ∃ μ, Set.subset (E.generalize.substitute μ) G := by
  constructor
  · exact entailment_has_instance_subgraph
  · rintro ⟨μ, h⟩
    exact instance_subgraph_entails G E μ h

theorem ordinary_interpolation_instances (G : GeneralizedGraph Iri Literal B)
    (E : Graph Iri Literal B) :
    SimplyEntails.{u} G E.generalize ↔ ∃ H, IsInstance H E.generalize ∧ Set.subset H G := by
  rw [ordinary_interpolation]
  constructor
  · rintro ⟨μ, h⟩
    exact ⟨E.generalize.substitute μ, ⟨μ, rfl⟩, h⟩
  · rintro ⟨H, ⟨μ, rfl⟩, h⟩
    exact ⟨μ, h⟩

/-- A ground conclusion is entailed exactly when it is a subgraph. -/
theorem ground_entailment_iff_subset (G E : GeneralizedGraph Iri Literal B) (hE : E.ground) :
    SimplyEntails.{u} G E ↔ Set.subset E G := by
  constructor
  · intro h
    obtain ⟨μ, hm⟩ := entailment_has_instance_subgraph h
    simpa only [ground_substitute E hE μ] using hm
  · exact subgraph_entailment

end RDF11
