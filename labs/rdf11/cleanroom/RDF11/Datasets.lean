/-
RDF 1.1 Concepts §4, incorporated by Semantics §10.
One blank domain is shared by graph names and all graph contents.
A present empty named graph is distinct from an absent graph name.
No dataset satisfaction relation or name/graph denotation equation is imposed.
-/
import RDF11.Instances

namespace RDF11

def Subject.mapBlank (f : A → B) : Subject Iri A → Subject Iri B
  | .iri i => .iri i
  | .blank b => .blank (f b)

theorem Subject.toTerm_mapBlank (f : A → B) (s : Subject Iri A) :
    (s.mapBlank f).toTerm = (s.toTerm : Term Iri Literal A).mapBlank f := by
  cases s <;> rfl

theorem Subject.mapBlank_comp (f : A → B) (g : B → C) (s : Subject Iri A) :
    (s.mapBlank f).mapBlank g = s.mapBlank (g ∘ f) := by
  cases s <;> rfl

theorem Subject.mapBlank_id (s : Subject Iri B) : s.mapBlank id = s := by
  cases s <;> rfl

theorem Subject.mapBlank_of_fixes (f : B → B) (s : Subject Iri B)
    (h : ∀ b, (s.toTerm : Term Iri Literal B).hasBlank b → f b = b) :
    s.mapBlank f = s := by
  cases s with
  | iri i => rfl
  | blank b => exact congrArg Subject.blank (h b rfl)

def Triple.mapBlank (f : A → B) (t : Triple Iri Literal A) : Triple Iri Literal B :=
  ⟨t.subject.mapBlank f, t.predicate, t.object.mapBlank f⟩

theorem Triple.generalize_mapBlank (f : A → B) (t : Triple Iri Literal A) :
    (t.mapBlank f).generalize = t.generalize.mapBlank f := by
  simp [mapBlank, generalize, GeneralizedTriple.mapBlank, Subject.toTerm_mapBlank,
    Term.mapBlank]

theorem Triple.generalize_injective {s t : Triple Iri Literal B}
    (h : s.generalize = t.generalize) : s = t := by
  cases s with
  | mk ss sp so =>
    cases t with
    | mk ts tp to =>
      cases ss <;> cases ts <;> simp_all [generalize, Subject.toTerm]

def Graph.mapBlank (f : A → B) (G : Graph Iri Literal A) : Graph Iri Literal B :=
  Set.image (Triple.mapBlank f) G

theorem Graph.generalize_mapBlank (f : A → B) (G : Graph Iri Literal A) :
    (G.mapBlank f).generalize = G.generalize.mapBlank f := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s.generalize, ⟨s, hs, rfl⟩, (s.generalize_mapBlank f).symm⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s.mapBlank f, ⟨s, hs, rfl⟩, s.generalize_mapBlank f⟩

theorem Graph.generalize_injective {G H : Graph Iri Literal B}
    (h : G.generalize = H.generalize) : G = H := by
  have inclusion {G H : Graph Iri Literal B} (he : G.generalize = H.generalize) :
      Set.subset G H := by
    intro t ht
    have : H.generalize t.generalize := he ▸ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hst⟩ := this
    exact Triple.generalize_injective hst ▸ hs
  exact Set.ext fun t => ⟨inclusion h t, inclusion h.symm t⟩

theorem Graph.mapBlank_comp (f g : B → B) (G : Graph Iri Literal B) :
    (G.mapBlank f).mapBlank g = G.mapBlank (g ∘ f) := by
  apply Graph.generalize_injective
  simp only [generalize_mapBlank, GeneralizedGraph.mapBlank_comp]

theorem Graph.mapBlank_of_fixes (f : B → B) (G : Graph Iri Literal B)
    (h : ∀ b, G.generalize.hasBlank b → f b = b) : G.mapBlank f = G := by
  apply Graph.generalize_injective
  rw [generalize_mapBlank, GeneralizedGraph.mapBlank_of_fixes f _ h]

theorem Graph.mapBlank_id (G : Graph Iri Literal B) : G.mapBlank id = G :=
  G.mapBlank_of_fixes id (fun _ _ => rfl)

theorem Term.hasBlank_mapBlank (f : A → B) (t : Term Iri Literal A) (b : B) :
    (t.mapBlank f).hasBlank b ↔ ∃ a, t.hasBlank a ∧ f a = b := by
  cases t <;> simp [mapBlank, hasBlank]

theorem GeneralizedTriple.hasBlank_mapBlank (f : A → B)
    (t : GeneralizedTriple Iri Literal A) (b : B) :
    (t.mapBlank f).hasBlank b ↔ ∃ a, t.hasBlank a ∧ f a = b := by
  simp only [hasBlank, mapBlank, Term.hasBlank_mapBlank]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr (Or.inl ha), rfl⟩
    · exact ⟨a, Or.inr (Or.inr ha), rfl⟩
  · rintro ⟨a, ha | ha | ha, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)

theorem GeneralizedGraph.hasBlank_mapBlank (f : A → B)
    (G : GeneralizedGraph Iri Literal A) (b : B) :
    (G.mapBlank f).hasBlank b ↔ ∃ a, G.hasBlank a ∧ f a = b := by
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, hb⟩
    obtain ⟨a, ha, hfa⟩ := (t.hasBlank_mapBlank f b).mp hb
    exact ⟨a, ⟨t, ht, ha⟩, hfa⟩
  · rintro ⟨a, ⟨t, ht, ha⟩, rfl⟩
    exact ⟨t.mapBlank f, ⟨t, ht, rfl⟩, (t.hasBlank_mapBlank f (f a)).mpr ⟨a, ha, rfl⟩⟩

/-- Graph names have precisely the IRI-or-blank alternatives of ordinary subjects. -/
abbrev GraphName (Iri B : Type) := Subject Iri B

structure Dataset (Iri Literal B : Type) where
  defaultGraph : Graph Iri Literal B
  namedGraphs : GraphName Iri B → Option (Graph Iri Literal B)

def Dataset.HasNamedGraph (D : Dataset Iri Literal B)
    (n : GraphName Iri B) (G : Graph Iri Literal B) : Prop := D.namedGraphs n = some G

theorem Dataset.name_unique (D : Dataset Iri Literal B) (n : GraphName Iri B)
    {G H : Graph Iri Literal B} (hG : D.HasNamedGraph n G) (hH : D.HasNamedGraph n H) :
    G = H := Option.some.inj (hG.symm.trans hH)

/-- Construct the partial lookup from the source's name/graph pairs and uniqueness law. -/
noncomputable def Dataset.ofPairs (defaultGraph : Graph Iri Literal B)
    (pairs : GraphName Iri B → Graph Iri Literal B → Prop)
    (_unique : ∀ n G H, pairs n G → pairs n H → G = H) : Dataset Iri Literal B := by
  classical
  exact ⟨defaultGraph, fun n => if h : ∃ G, pairs n G then some (Classical.choose h) else none⟩

theorem Dataset.ofPairs_named_iff (defaultGraph : Graph Iri Literal B)
    (pairs : GraphName Iri B → Graph Iri Literal B → Prop)
    (unique : ∀ n G H, pairs n G → pairs n H → G = H)
    (n : GraphName Iri B) (G : Graph Iri Literal B) :
    (Dataset.ofPairs defaultGraph pairs unique).HasNamedGraph n G ↔ pairs n G := by
  classical
  by_cases h : ∃ H, pairs n H
  · simp only [HasNamedGraph, ofPairs, dif_pos h, Option.some.injEq]
    exact ⟨fun he => he ▸ Classical.choose_spec h,
      fun hG => unique n _ G (Classical.choose_spec h) hG⟩
  · have hn : ¬ pairs n G := fun hG => h ⟨G, hG⟩
    simp [HasNamedGraph, ofPairs, h, hn]

def Dataset.hasBlank (D : Dataset Iri Literal B) (b : B) : Prop :=
  D.defaultGraph.generalize.hasBlank b ∨
    ∃ n G, D.HasNamedGraph n G ∧
      ((n.toTerm : Term Iri Literal B).hasBlank b ∨ G.generalize.hasBlank b)

def Dataset.HasName (D : Dataset Iri Literal B) (n : GraphName Iri B) : Prop :=
  ∃ G, D.HasNamedGraph n G

def Dataset.quads (D : Dataset Iri Literal B)
    (n : GraphName Iri B) (t : Triple Iri Literal B) : Prop :=
  ∃ G, D.HasNamedGraph n G ∧ G t

def Dataset.empty : Dataset Iri Literal B := ⟨Set.empty, fun _ => none⟩

noncomputable def Dataset.emptyNamed (n : GraphName Iri B) : Dataset Iri Literal B := by
  classical
  exact ⟨Set.empty, fun m => if m = n then some Set.empty else none⟩

theorem Dataset.emptyNamed_present (n : GraphName Iri B) :
    (Dataset.emptyNamed n : Dataset Iri Literal B).HasNamedGraph n Set.empty := by
  simp [emptyNamed, HasNamedGraph]

theorem Dataset.emptyNamed_ne_empty (n : GraphName Iri B) :
    (Dataset.emptyNamed n : Dataset Iri Literal B) ≠ Dataset.empty := by
  intro h
  have hp := Dataset.emptyNamed_present (Literal := Literal) n
  rw [h] at hp
  cases hp

theorem Dataset.emptyNamed_same_quads (n : GraphName Iri B) :
    (Dataset.emptyNamed n : Dataset Iri Literal B).quads = Dataset.empty.quads := by
  classical
  funext m t
  apply propext
  simp [quads, HasNamedGraph, emptyNamed, empty, Set.empty]

/-- Full dataset equality requires graph-name presence as well as quad membership. -/
theorem Dataset.eq_of_default_names_quads (D E : Dataset Iri Literal B)
    (hd : D.defaultGraph = E.defaultGraph)
    (hn : ∀ n, D.HasName n ↔ E.HasName n)
    (hq : D.quads = E.quads) : D = E := by
  have named : D.namedGraphs = E.namedGraphs := by
    funext n
    cases hD : D.namedGraphs n with
    | none =>
      cases hE : E.namedGraphs n with
      | none => rfl
      | some G =>
        obtain ⟨H, hH⟩ := (hn n).mpr ⟨G, hE⟩
        simp [HasNamedGraph, hD] at hH
    | some G =>
      obtain ⟨H, hH⟩ := (hn n).mp ⟨G, hD⟩
      have eqGH : G = H := by
        apply Set.ext
        intro t
        constructor
        · intro ht
          have : E.quads n t := hq ▸ ⟨G, hD, ht⟩
          obtain ⟨K, hK, hKt⟩ := this
          exact E.name_unique n hK hH ▸ hKt
        · intro ht
          have : D.quads n t := hq ▸ (show E.quads n t from ⟨H, hH, ht⟩)
          obtain ⟨K, hK, hKt⟩ := this
          exact D.name_unique n hK hD ▸ hKt
      change some G = _
      rw [hH, eqGH]
  cases D
  cases E
  cases hd
  cases named
  rfl

end RDF11
