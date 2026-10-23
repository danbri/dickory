/-
RDF 1.1 Semantics, informative Appendix B: pre-interpretations on vocabulary V.
Reuse §5 literally on the restricted name domains, preserving IR, IP and partial IL.
Completion here changes only the name mappings. No finite-carrier bound is claimed.
-/
import RDF11.NameMaps
import RDF11.Vocabulary
import RDF11.FiniteEntailment
import RDF11.Transformations

namespace RDF11

abbrev VocabularyIRI (V : Set (Name Iri Literal)) := {i : Iri // V (.inl i)}
abbrev VocabularyLiteral (V : Set (Name Iri Literal)) := {l : Literal // V (.inr l)}

/-- V restricts the name domains, not the resource universe or blank identities. -/
abbrev PreInterpretation (V : Set (Name Iri Literal)) (U : Type u) :=
  SimpleInterpretation (VocabularyIRI V) (VocabularyLiteral V) U

namespace PreInterpretation

/-- Complete IS using an existing resource; leave out-of-V literals undefined. -/
noncomputable def extend {V : Set (Name Iri Literal)} (I : PreInterpretation V U) :
    SimpleInterpretation Iri Literal U := by
  classical
  exact {
    IR := I.IR
    IR_nonempty := I.IR_nonempty
    IP := I.IP
    IEXT := I.IEXT
    IS := fun i => if h : V (.inl i) then I.IS ⟨i, h⟩ else
      ⟨Classical.choose I.IR_nonempty, Or.inl (Classical.choose_spec I.IR_nonempty)⟩
    IL := fun l => if h : V (.inr l) then I.IL ⟨l, h⟩ else none
  }

theorem restrict_extend {V : Set (Name Iri Literal)} (I : PreInterpretation V U) :
    I.extend.comapNames (fun i : VocabularyIRI V => i.val)
      (fun l : VocabularyLiteral V => l.val) = I := by
  cases I
  simp only [extend, SimpleInterpretation.comapNames, Function.comp_def]
  congr 1 <;> funext x <;> simp [x.property]

theorem satisfies_extend {V : Set (Name Iri Literal)} (I : PreInterpretation V U)
    (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B) :
    I.extend.Satisfies (G.mapNames Subtype.val Subtype.val) ↔ I.Satisfies G := by
  rw [I.extend.satisfies_mapNames, I.restrict_extend]

theorem denote_extend {V : Set (Name Iri Literal)} (I : PreInterpretation V U)
    (A : I.Assignment B) (t : Term (VocabularyIRI V) (VocabularyLiteral V) B) :
    I.extend.denote A (t.mapNames Subtype.val Subtype.val) = I.denote A t := by
  cases t with
  | iri i => simp [Term.mapNames, SimpleInterpretation.denote, extend, i.property]
  | literal l => simp [Term.mapNames, SimpleInterpretation.denote, extend, l.property]
  | blank b => rfl

theorem tripleTrue_extend {V : Set (Name Iri Literal)} (I : PreInterpretation V U)
    (A : I.Assignment B) (t : GeneralizedTriple (VocabularyIRI V) (VocabularyLiteral V) B) :
    I.extend.TripleTrue A (t.mapNames Subtype.val Subtype.val) ↔ I.TripleTrue A t := by
  simp only [SimpleInterpretation.TripleTrue, GeneralizedTriple.mapNames, denote_extend]
  rfl

theorem graphTrue_extend {V : Set (Name Iri Literal)} (I : PreInterpretation V U)
    (A : I.Assignment B) (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B) :
    I.extend.GraphTrue A (G.mapNames Subtype.val Subtype.val) ↔ I.GraphTrue A G := by
  constructor
  · intro h t ht
    exact (I.tripleTrue_extend A t).mp (h _ ⟨t, ht, rfl⟩)
  · rintro h _ ⟨t, ht, rfl⟩
    exact (I.tripleTrue_extend A t).mpr (h t ht)

/-- Any same-carrier completion whose restriction is I preserves satisfaction. -/
theorem satisfies_of_restriction {V : Set (Name Iri Literal)} (I : PreInterpretation V U)
    (J : SimpleInterpretation Iri Literal U)
    (h : J.comapNames (fun i : VocabularyIRI V => i.val)
      (fun l : VocabularyLiteral V => l.val) = I)
    (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B) :
    J.Satisfies (G.mapNames Subtype.val Subtype.val) ↔ I.Satisfies G := by
  rw [J.satisfies_mapNames, h]

theorem satisfiable_iff {V : Set (Name Iri Literal)}
    (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B) :
    SimplySatisfiable.{u} G ↔ SimplySatisfiable.{u} (G.mapNames Subtype.val Subtype.val) := by
  constructor
  · rintro ⟨U, I, h⟩
    exact ⟨U, extend I, (satisfies_extend I G).mpr h⟩
  · rintro ⟨U, I, h⟩
    exact ⟨U, I.comapNames Subtype.val Subtype.val, (I.satisfies_mapNames _ _ G).mp h⟩

/-- Quantifies over all pre-interpretations, not only ones with finite IR. -/
theorem entails_iff {V : Set (Name Iri Literal)}
    (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B₁)
    (E : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B₂) :
    SimplyEntails.{u} G E ↔
      SimplyEntails.{u} (G.mapNames Subtype.val Subtype.val) (E.mapNames Subtype.val Subtype.val) := by
  constructor
  · exact simplyEntails_mapNames Subtype.val Subtype.val
  · intro h U I hG
    exact (satisfies_extend I E).mp (h U (extend I) ((satisfies_extend I G).mpr hG))

end PreInterpretation

/-- Convert an ambient term to its names in V, using explicit occurrence evidence. -/
def Term.restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (t : Term Iri Literal B) (h : Set.subset (t.names datatype) V) :
    Term (VocabularyIRI V) (VocabularyLiteral V) B :=
  match t with
  | .iri i => .iri ⟨i, h _ rfl⟩
  | .literal l => .literal ⟨l, h _ (Or.inl rfl)⟩
  | .blank b => .blank b

theorem Term.include_restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (t : Term Iri Literal B) (h : Set.subset (t.names datatype) V) :
    (t.restrictNames datatype V h).mapNames Subtype.val Subtype.val = t := by
  cases t <;> rfl

def GeneralizedTriple.restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (t : GeneralizedTriple Iri Literal B) (h : Set.subset (t.names datatype) V) :
    GeneralizedTriple (VocabularyIRI V) (VocabularyLiteral V) B :=
  ⟨t.subject.restrictNames datatype V (fun n hn => h n (Or.inl hn)),
   t.predicate.restrictNames datatype V (fun n hn => h n (Or.inr (Or.inl hn))),
   t.object.restrictNames datatype V (fun n hn => h n (Or.inr (Or.inr hn)))⟩

theorem GeneralizedTriple.include_restrictNames (datatype : Literal → Iri)
    (V : Set (Name Iri Literal)) (t : GeneralizedTriple Iri Literal B)
    (h : Set.subset (t.names datatype) V) :
    (t.restrictNames datatype V h).mapNames Subtype.val Subtype.val = t := by
  exact congr (congr (congrArg GeneralizedTriple.mk
    (t.subject.include_restrictNames datatype V _))
    (t.predicate.include_restrictNames datatype V _))
    (t.object.include_restrictNames datatype V _)

def GeneralizedGraph.restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (G : GeneralizedGraph Iri Literal B) (h : Set.subset (G.vocabulary datatype) V) :
    GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B :=
  fun q => ∃ (t : GeneralizedTriple Iri Literal B) (ht : G t),
    t.restrictNames datatype V (fun n hn => h n ⟨t, ht, hn⟩) = q

theorem GeneralizedGraph.include_restrictNames (datatype : Literal → Iri)
    (V : Set (Name Iri Literal)) (G : GeneralizedGraph Iri Literal B)
    (h : Set.subset (G.vocabulary datatype) V) :
    (G.restrictNames datatype V h).mapNames Subtype.val Subtype.val = G := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, he⟩
    have eq : q = t := (q.include_restrictNames datatype V _).symm.trans he
    exact eq ▸ hq
  · intro ht
    exact ⟨_, ⟨t, ht, rfl⟩, t.include_restrictNames datatype V _⟩

theorem preinterpretation_entailment_iff (datatype : Literal → Iri)
    (V : Set (Name Iri Literal)) (G : GeneralizedGraph Iri Literal B₁)
    (E : GeneralizedGraph Iri Literal B₂)
    (hG : Set.subset (G.vocabulary datatype) V) (hE : Set.subset (E.vocabulary datatype) V) :
    SimplyEntails.{u} (G.restrictNames datatype V hG) (E.restrictNames datatype V hE) ↔
      SimplyEntails.{u} G E := by
  rw [PreInterpretation.entails_iff, G.include_restrictNames, E.include_restrictNames]

theorem preinterpretation_satisfiable_iff (datatype : Literal → Iri)
    (V : Set (Name Iri Literal)) (G : GeneralizedGraph Iri Literal B)
    (hG : Set.subset (G.vocabulary datatype) V) :
    SimplySatisfiable.{u} (G.restrictNames datatype V hG) ↔ SimplySatisfiable.{u} G := by
  rw [PreInterpretation.satisfiable_iff, G.include_restrictNames]

def Term.nameList (datatype : Literal → Iri) : Term Iri Literal B → List (Name Iri Literal)
  | .iri i => [.inl i]
  | .literal l => [.inr l, .inl (datatype l)]
  | .blank _ => []

theorem Term.mem_nameList (datatype : Literal → Iri) (t : Term Iri Literal B)
    (n : Name Iri Literal) : n ∈ t.nameList datatype ↔ t.names datatype n := by
  cases t <;> simp [nameList, names, Set.empty]

def GeneralizedTriple.nameList (datatype : Literal → Iri)
    (t : GeneralizedTriple Iri Literal B) : List (Name Iri Literal) :=
  t.subject.nameList datatype ++ t.predicate.nameList datatype ++ t.object.nameList datatype

theorem GeneralizedTriple.mem_nameList (datatype : Literal → Iri)
    (t : GeneralizedTriple Iri Literal B) (n : Name Iri Literal) :
    n ∈ t.nameList datatype ↔ t.names datatype n := by
  simp [nameList, names, Term.mem_nameList]

theorem finite_vocabulary_of_finite_graph (datatype : Literal → Iri)
    (G : GeneralizedGraph Iri Literal B) (hG : FiniteGraph G) :
    Nonempty (Enumeration (G.vocabulary datatype)) := by
  classical
  obtain ⟨e⟩ := hG
  let en := Enumeration.fromList (e.triples.flatMap (GeneralizedTriple.nameList datatype))
  refine ⟨⟨en.triples, en.nodup, ?_⟩⟩
  intro n
  rw [en.membership]
  change n ∈ e.triples.flatMap (GeneralizedTriple.nameList datatype) ↔
    ∃ t, G t ∧ t.names datatype n
  simp only [List.mem_flatMap, GeneralizedTriple.mem_nameList, e.membership]

/-- Two finite graphs share a finite vocabulary, including datatype IRI names. -/
theorem finite_shared_vocabulary (datatype : Literal → Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : FiniteGraph G) (hE : FiniteGraph E) :
    Nonempty (Enumeration (Set.union (G.vocabulary datatype) (E.vocabulary datatype))) := by
  classical
  obtain ⟨g⟩ := finite_vocabulary_of_finite_graph datatype G hG
  obtain ⟨e⟩ := finite_vocabulary_of_finite_graph datatype E hE
  let v := Enumeration.fromList (g.triples ++ e.triples)
  refine ⟨⟨v.triples, v.nodup, ?_⟩⟩
  intro n
  rw [v.membership]
  exact (List.mem_append).trans (or_congr (g.membership n) (e.membership n))

/-- Finite name vocabulary suffices for comparison; IR is still unrestricted. -/
theorem finite_vocabulary_comparison (datatype : Literal → Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : FiniteGraph G) (hE : FiniteGraph E) :
    let V := Set.union (G.vocabulary datatype) (E.vocabulary datatype)
    Nonempty (Enumeration V) ∧
      (SimplyEntails.{u} (G.restrictNames datatype V (fun _ h => Or.inl h))
        (E.restrictNames datatype V (fun _ h => Or.inr h)) ↔ SimplyEntails.{u} G E) :=
  ⟨finite_shared_vocabulary datatype G E hG hE,
    preinterpretation_entailment_iff datatype _ G E _ _⟩

end RDF11
