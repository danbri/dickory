/-
RDF 1.1 Semantics §4.1: union as an instance of merge, and the unshared case.
The common ambient sum lets the existing instance/isomorphism relations compare
original identities with fresh copies, without assuming spare original blanks.
-/
import RDF11.FamilyMerge

namespace RDF11.GraphFamily

variable {K Iri Literal B : Type}

theorem mapBlank_union (f : B → C) (G : K → GeneralizedGraph Iri Literal B) :
    GeneralizedGraph.mapBlank f (Set.iUnion G) =
      Set.iUnion (fun i => (G i).mapBlank f) :=
  Set.image_iUnion (GeneralizedTriple.mapBlank f) G

theorem forget_tags (G : K → GeneralizedGraph Iri Literal B) :
    (merge G).mapBlank (fun b => b.2) = Set.iUnion G := by
  rw [merge, mapBlank_union]
  simp only [GeneralizedGraph.mapBlank_comp, Function.comp_def]
  change (Set.iUnion fun i => (G i).mapBlank id) = Set.iUnion G
  simp only [GeneralizedGraph.mapBlank_id]

abbrev ScopedBlank (K B : Type) := Sum B (Sigma (fun _ : K => B))

def scopedUnion (G : K → GeneralizedGraph Iri Literal B) :
    GeneralizedGraph Iri Literal (ScopedBlank K B) :=
  GeneralizedGraph.mapBlank Sum.inl (Set.iUnion G)

def scopedMerge (G : K → GeneralizedGraph Iri Literal B) :
    GeneralizedGraph Iri Literal (ScopedBlank K B) := (merge G).mapBlank Sum.inr

def forget : ScopedBlank K B → ScopedBlank K B
  | .inl b => .inl b
  | .inr b => .inl b.2

theorem forget_scopedMerge (G : K → GeneralizedGraph Iri Literal B) :
    (scopedMerge G).mapBlank forget = scopedUnion G := by
  rw [scopedMerge, GeneralizedGraph.mapBlank_comp]
  change (merge G).mapBlank (Sum.inl ∘ fun b => b.2) = _
  rw [← GeneralizedGraph.mapBlank_comp, forget_tags]
  rfl

theorem union_is_instance (G : K → GeneralizedGraph Iri Literal B) :
    IsInstance (scopedUnion G) (scopedMerge G) := by
  simpa only [forget_scopedMerge] using mapBlank_is_instance forget (scopedMerge G)

noncomputable def restore (G : K → GeneralizedGraph Iri Literal B) :
    ScopedBlank K B → ScopedBlank K B := by
  classical
  exact fun b => match b with
    | .inl a => if h : ∃ i, (G i).hasBlank a then .inr ⟨Classical.choose h, a⟩ else .inl a
    | .inr a => .inr a

theorem restore_forget (G : K → GeneralizedGraph Iri Literal B) (hG : Apart G)
    (b : ScopedBlank K B) (hb : (scopedMerge G).hasBlank b) :
    restore G (forget b) = b := by
  obtain ⟨a, ha, rfl⟩ := ((merge G).hasBlank_mapBlank Sum.inr b).mp hb
  have hi := (merge_hasBlank G a).mp ha
  have hex : ∃ i, (G i).hasBlank a.2 := ⟨a.1, hi⟩
  have he : Classical.choose hex = a.1 := hG _ _ _ (Classical.choose_spec hex) hi
  simp only [forget, restore, dif_pos hex, he]

theorem forget_restore (G : K → GeneralizedGraph Iri Literal B)
    (b : ScopedBlank K B) (hb : (scopedUnion G).hasBlank b) :
    forget (restore G b) = b := by
  obtain ⟨a, ha, rfl⟩ :=
    (GeneralizedGraph.hasBlank_mapBlank Sum.inl (Set.iUnion G) b).mp hb
  have hex := (union_hasBlank G a).mp ha
  simp only [restore, dif_pos hex, forget]

/-- The source treats isomorphic graphs as identical; fresh tags are a representative. -/
noncomputable def apart_isomorphism (G : K → GeneralizedGraph Iri Literal B)
    (hG : Apart G) : GraphIsomorphism (scopedMerge G) (scopedUnion G) where
  toFun := forget
  invFun := restore G
  left_inv := restore_forget G hG
  right_inv := forget_restore G
  image_eq := forget_scopedMerge G

theorem apart_mutual_instances (G : K → GeneralizedGraph Iri Literal B)
    (hG : Apart G) :
    IsInstance (scopedUnion G) (scopedMerge G) ∧
      IsInstance (scopedMerge G) (scopedUnion G) :=
  (apart_isomorphism G hG).mutual_instances

end RDF11.GraphFamily
