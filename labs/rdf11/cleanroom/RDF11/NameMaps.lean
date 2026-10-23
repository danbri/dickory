/-
Name-domain transport for Appendix B's vocabulary-restricted interpretations.
These maps change the name types without changing any blank-node identity.
Pullback preserves §5's typed IR/IP distinction and partial literal denotation.
-/
import RDF11.Entailment

namespace RDF11

def Term.mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂) :
    Term Iri₁ Literal₁ B → Term Iri₂ Literal₂ B
  | .iri i => .iri (f i)
  | .literal l => .literal (g l)
  | .blank b => .blank b

def Subject.mapNames (f : Iri₁ → Iri₂) : Subject Iri₁ B → Subject Iri₂ B
  | .iri i => .iri (f i)
  | .blank b => .blank b

def Triple.mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂)
    (t : Triple Iri₁ Literal₁ B) : Triple Iri₂ Literal₂ B :=
  ⟨t.subject.mapNames f, f t.predicate, t.object.mapNames f g⟩

def GeneralizedTriple.mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂)
    (t : GeneralizedTriple Iri₁ Literal₁ B) : GeneralizedTriple Iri₂ Literal₂ B :=
  ⟨t.subject.mapNames f g, t.predicate.mapNames f g, t.object.mapNames f g⟩

def Graph.mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂)
    (G : Graph Iri₁ Literal₁ B) : Graph Iri₂ Literal₂ B :=
  Set.image (Triple.mapNames f g) G

def GeneralizedGraph.mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂)
    (G : GeneralizedGraph Iri₁ Literal₁ B) : GeneralizedGraph Iri₂ Literal₂ B :=
  Set.image (GeneralizedTriple.mapNames f g) G

theorem Triple.generalize_mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂)
    (t : Triple Iri₁ Literal₁ B) :
    (t.mapNames f g).generalize = t.generalize.mapNames f g := by
  cases t with
  | mk s p o => cases s <;> rfl

theorem Graph.generalize_mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂)
    (G : Graph Iri₁ Literal₁ B) :
    (G.mapNames f g).generalize = G.generalize.mapNames f g := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.generalize, ⟨q, hq, rfl⟩, (q.generalize_mapNames f g).symm⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.mapNames f g, ⟨q, hq, rfl⟩, q.generalize_mapNames f g⟩

namespace SimpleInterpretation

/-- Pull back only name denotations; keep resources and property extensions. -/
def comapNames (I : SimpleInterpretation Iri₂ Literal₂ U)
    (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂) : SimpleInterpretation Iri₁ Literal₁ U where
  IR := I.IR
  IR_nonempty := I.IR_nonempty
  IP := I.IP
  IEXT := I.IEXT
  IS := I.IS ∘ f
  IL := I.IL ∘ g

theorem denote_mapNames (I : SimpleInterpretation Iri₂ Literal₂ U)
    (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂) (A : I.Assignment B)
    (t : Term Iri₁ Literal₁ B) :
    I.denote A (t.mapNames f g) = (I.comapNames f g).denote A t := by
  cases t <;> rfl

theorem tripleTrue_mapNames (I : SimpleInterpretation Iri₂ Literal₂ U)
    (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂) (A : I.Assignment B)
    (t : GeneralizedTriple Iri₁ Literal₁ B) :
    I.TripleTrue A (t.mapNames f g) ↔ (I.comapNames f g).TripleTrue A t := by
  simp only [TripleTrue, GeneralizedTriple.mapNames, denote_mapNames]
  rfl

theorem graphTrue_mapNames (I : SimpleInterpretation Iri₂ Literal₂ U)
    (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂) (A : I.Assignment B)
    (G : GeneralizedGraph Iri₁ Literal₁ B) :
    I.GraphTrue A (G.mapNames f g) ↔ (I.comapNames f g).GraphTrue A G := by
  constructor
  · intro h t ht
    exact (I.tripleTrue_mapNames f g A t).mp (h _ ⟨t, ht, rfl⟩)
  · rintro h _ ⟨t, ht, rfl⟩
    exact (I.tripleTrue_mapNames f g A t).mpr (h t ht)

theorem satisfies_mapNames (I : SimpleInterpretation Iri₂ Literal₂ U)
    (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂) (G : GeneralizedGraph Iri₁ Literal₁ B) :
    I.Satisfies (G.mapNames f g) ↔ (I.comapNames f g).Satisfies G := by
  rw [I.satisfies_iff_exists_graphTrue, (I.comapNames f g).satisfies_iff_exists_graphTrue]
  exact exists_congr (fun A => I.graphTrue_mapNames f g A G)

end SimpleInterpretation

theorem simplyEntails_mapNames (f : Iri₁ → Iri₂) (g : Literal₁ → Literal₂)
    {G : GeneralizedGraph Iri₁ Literal₁ B₁} {E : GeneralizedGraph Iri₁ Literal₁ B₂}
    (h : SimplyEntails.{u} G E) : SimplyEntails.{u} (G.mapNames f g) (E.mapNames f g) := by
  intro U I hG
  exact (I.satisfies_mapNames f g E).mpr (h U (I.comapNames f g)
    ((I.satisfies_mapNames f g G).mp hG))

end RDF11
