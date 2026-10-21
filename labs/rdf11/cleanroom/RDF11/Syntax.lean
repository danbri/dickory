/-
MT11-TRIPLE-TERM-DOMAINS, MT11-GENERALIZED-SYNTAX, MT11-GRAPH-SET.
IRI and literal domains are abstract parameters imported from Concepts.
Their concrete lexical admissibility is an explicit external obligation.
Blank-node identities are abstract; they are not serialization labels.
-/
import RDF11.Set

namespace RDF11

inductive Term (Iri Literal Blank : Type) where
  | iri : Iri → Term Iri Literal Blank
  | literal : Literal → Term Iri Literal Blank
  | blank : Blank → Term Iri Literal Blank
  deriving DecidableEq

inductive Subject (Iri Blank : Type) where
  | iri : Iri → Subject Iri Blank
  | blank : Blank → Subject Iri Blank
  deriving DecidableEq

def Subject.toTerm : Subject Iri Blank → Term Iri Literal Blank
  | .iri i => .iri i
  | .blank b => .blank b

structure Triple (Iri Literal Blank : Type) where
  subject : Subject Iri Blank
  predicate : Iri
  object : Term Iri Literal Blank
  deriving DecidableEq

structure GeneralizedTriple (Iri Literal Blank : Type) where
  subject : Term Iri Literal Blank
  predicate : Term Iri Literal Blank
  object : Term Iri Literal Blank
  deriving DecidableEq

def Triple.generalize (t : Triple Iri Literal Blank) : GeneralizedTriple Iri Literal Blank :=
  ⟨t.subject.toTerm, .iri t.predicate, t.object⟩

abbrev Graph (Iri Literal Blank : Type) := Set (Triple Iri Literal Blank)
abbrev GeneralizedGraph (Iri Literal Blank : Type) := Set (GeneralizedTriple Iri Literal Blank)

def Graph.generalize (g : Graph Iri Literal Blank) : GeneralizedGraph Iri Literal Blank :=
  Set.image Triple.generalize g

def Term.hasBlank (b : Blank) : Term Iri Literal Blank → Prop
  | .blank c => c = b
  | .iri _ | .literal _ => False

def GeneralizedTriple.hasBlank (b : Blank) (t : GeneralizedTriple Iri Literal Blank) : Prop :=
  t.subject.hasBlank b ∨ t.predicate.hasBlank b ∨ t.object.hasBlank b

def GeneralizedGraph.hasBlank (g : GeneralizedGraph Iri Literal Blank) (b : Blank) : Prop :=
  ∃ t, g t ∧ t.hasBlank b

def GeneralizedGraph.ground (g : GeneralizedGraph Iri Literal Blank) : Prop :=
  ∀ b, ¬ g.hasBlank b

def Term.hasLiteral (l : Literal) : Term Iri Literal Blank → Prop
  | .literal k => k = l
  | .iri _ | .blank _ => False

def GeneralizedTriple.hasLiteral (l : Literal) (t : GeneralizedTriple Iri Literal Blank) : Prop :=
  t.subject.hasLiteral l ∨ t.predicate.hasLiteral l ∨ t.object.hasLiteral l

def Term.mapBlank (f : A → B) : Term Iri Literal A → Term Iri Literal B
  | .iri i => .iri i
  | .literal l => .literal l
  | .blank b => .blank (f b)

def GeneralizedTriple.mapBlank (f : A → B) (t : GeneralizedTriple Iri Literal A) :
    GeneralizedTriple Iri Literal B :=
  ⟨t.subject.mapBlank f, t.predicate.mapBlank f, t.object.mapBlank f⟩

def GeneralizedGraph.mapBlank (f : A → B) (g : GeneralizedGraph Iri Literal A) :
    GeneralizedGraph Iri Literal B := Set.image (GeneralizedTriple.mapBlank f) g

@[simp] theorem Term.mapBlank_id (t : Term Iri Literal A) : t.mapBlank id = t := by
  cases t <;> rfl

theorem Term.mapBlank_comp (f : A → B) (h : B → C) (t : Term Iri Literal A) :
    (t.mapBlank f).mapBlank h = t.mapBlank (h ∘ f) := by
  cases t <;> rfl

theorem GeneralizedTriple.mapBlank_id (t : GeneralizedTriple Iri Literal A) :
    t.mapBlank id = t := by
  cases t
  simp [mapBlank]

theorem GeneralizedTriple.mapBlank_comp (f : A → B) (h : B → C)
    (t : GeneralizedTriple Iri Literal A) :
    (t.mapBlank f).mapBlank h = t.mapBlank (h ∘ f) := by
  cases t
  simp [mapBlank, Term.mapBlank_comp]

theorem GeneralizedGraph.mapBlank_id (g : GeneralizedGraph Iri Literal A) :
    g.mapBlank id = g := by
  apply Set.ext
  intro t
  simp [mapBlank, Set.image, GeneralizedTriple.mapBlank_id]

end RDF11
