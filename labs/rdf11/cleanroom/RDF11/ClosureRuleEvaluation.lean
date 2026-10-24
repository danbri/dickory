/-
Executable one-round consequences, exactly matching RDFStep/RDFSStep.
All pairs are considered, including pairing a triple with itself. Literal
typing inspects only object position and recognized datatype identity.
-/
import RDF11.EntailmentClosure

namespace RDF11.ClosureEvaluation

def emit (condition : Prop) [Decidable condition] (t : GeneralizedTriple Iri Literal B) :
    List (GeneralizedTriple Iri Literal B) := if condition then [t] else []

theorem mem_emit (condition : Prop) [Decidable condition] (t q : GeneralizedTriple Iri Literal B) :
    q ∈ emit condition t ↔ condition ∧ q = t := by
  by_cases h : condition <;> simp [emit, h]

variable [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B]

def rdfUnary (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (t : GeneralizedTriple Iri Literal B) : List (GeneralizedTriple Iri Literal B) :=
  [⟨t.predicate, .iri (v.iri .rdfType), .iri (v.iri .rdfProperty)⟩] ++
    match t.object with
    | .literal l => emit (datatype l = v.iri .rdfLangString ∨ datatype l = v.iri .xsdString)
        ⟨.literal l, .iri (v.iri .rdfType), .iri (datatype l)⟩
    | _ => []

def rdfNext (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (xs : List (GeneralizedTriple Iri Literal B)) : List (GeneralizedTriple Iri Literal B) :=
  xs.flatMap (rdfUnary datatype v)

omit [DecidableEq Literal] [DecidableEq B] in
theorem rdfUnary_sound (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B) (t q : GeneralizedTriple Iri Literal B)
    (ht : G t) (hq : q ∈ rdfUnary T.literalSyntax.datatype v t) :
    RDFStep T v.baseDatatypes v G q := by
  rcases List.mem_append.mp hq with h | h
  · have he := List.mem_singleton.mp h
    subst q
    exact .rdfD2 t ht
  · obtain ⟨s, p, o⟩ := t
    cases o with
    | iri i => cases h
    | blank b => cases h
    | literal l =>
      obtain ⟨hd, rfl⟩ := (mem_emit _ _ q).mp h
      exact .GrdfD1 s p l ht hd

omit [DecidableEq Literal] [DecidableEq B] in
theorem rdfNext_iff (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (xs : List (GeneralizedTriple Iri Literal B)) (q : GeneralizedTriple Iri Literal B) :
    q ∈ rdfNext T.literalSyntax.datatype v xs ↔ RDFStep T v.baseDatatypes v (Set.ofList xs) q := by
  constructor
  · intro h
    obtain ⟨t, ht, hq⟩ := List.mem_flatMap.mp h
    exact rdfUnary_sound T v _ t q ht hq
  · intro h
    cases h with
    | rdfD2 t ht =>
      exact List.mem_flatMap.mpr ⟨t, ht, List.mem_append_left _ (by simp)⟩
    | GrdfD1 s p l ht hd =>
      apply List.mem_flatMap.mpr
      refine ⟨⟨s, p, .literal l⟩, ht, ?_⟩
      apply List.mem_append_right
      exact (mem_emit _ _ _).mpr ⟨hd, rfl⟩

def rdfsUnary (v : RDFSVocabulary Iri) (t : GeneralizedTriple Iri Literal B) :
    List (GeneralizedTriple Iri Literal B) :=
  [⟨t.subject, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .resource)⟩,
   ⟨t.object, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .resource)⟩] ++
  emit (t.predicate = .iri (v.iri (.rdf .rdfType)) ∧ t.object = .iri (v.iri (.rdf .rdfProperty)))
    ⟨t.subject, .iri (v.iri .subPropertyOf), t.subject⟩ ++
  emit (t.predicate = .iri (v.iri (.rdf .rdfType)) ∧ t.object = .iri (v.iri .class_))
    ⟨t.subject, .iri (v.iri .subClassOf), .iri (v.iri .resource)⟩ ++
  emit (t.predicate = .iri (v.iri (.rdf .rdfType)) ∧ t.object = .iri (v.iri .class_))
    ⟨t.subject, .iri (v.iri .subClassOf), t.subject⟩ ++
  emit (t.predicate = .iri (v.iri (.rdf .rdfType)) ∧ t.object = .iri (v.iri .containerMembershipProperty))
    ⟨t.subject, .iri (v.iri .subPropertyOf), .iri (v.iri .member)⟩ ++
  emit (t.predicate = .iri (v.iri (.rdf .rdfType)) ∧ t.object = .iri (v.iri .datatype))
    ⟨t.subject, .iri (v.iri .subClassOf), .iri (v.iri .literal)⟩

def rdfsBinary (v : RDFSVocabulary Iri)
    (t u : GeneralizedTriple Iri Literal B) : List (GeneralizedTriple Iri Literal B) :=
  emit (t.predicate = .iri (v.iri .domain) ∧ u.predicate = t.subject)
    ⟨u.subject, .iri (v.iri (.rdf .rdfType)), t.object⟩ ++
  emit (t.predicate = .iri (v.iri .range) ∧ u.predicate = t.subject)
    ⟨u.object, .iri (v.iri (.rdf .rdfType)), t.object⟩ ++
  emit (t.predicate = .iri (v.iri .subPropertyOf) ∧ u.predicate = .iri (v.iri .subPropertyOf) ∧ t.object = u.subject)
    ⟨t.subject, .iri (v.iri .subPropertyOf), u.object⟩ ++
  emit (t.predicate = .iri (v.iri .subPropertyOf) ∧ u.predicate = t.subject)
    ⟨u.subject, t.object, u.object⟩ ++
  emit (t.predicate = .iri (v.iri .subClassOf) ∧ u.predicate = .iri (v.iri (.rdf .rdfType)) ∧ u.object = t.subject)
    ⟨u.subject, .iri (v.iri (.rdf .rdfType)), t.object⟩ ++
  emit (t.predicate = .iri (v.iri .subClassOf) ∧ u.predicate = .iri (v.iri .subClassOf) ∧ t.object = u.subject)
    ⟨t.subject, .iri (v.iri .subClassOf), u.object⟩

def rdfsZero (v : RDFSVocabulary Iri) : List (GeneralizedTriple Iri Literal B) :=
  [v.iri (.rdf .rdfLangString), v.iri (.rdf .xsdString)].map
    (fun a => ⟨.iri a, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .datatype)⟩)

def rdfsNext (v : RDFSVocabulary Iri) (xs : List (GeneralizedTriple Iri Literal B)) :
    List (GeneralizedTriple Iri Literal B) :=
  rdfsZero v ++ xs.flatMap (rdfsUnary v) ++ xs.flatMap (fun t => xs.flatMap (rdfsBinary v t))

theorem rdfsUnary_sound (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B) (t q : GeneralizedTriple Iri Literal B)
    (ht : G t) (hq : q ∈ rdfsUnary v t) : RDFSStep T D v G q := by
  simp only [rdfsUnary, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, mem_emit, or_assoc] at hq
  rcases hq with rfl | rfl | ⟨⟨hp, ho⟩, rfl⟩ | ⟨⟨hp, ho⟩, rfl⟩ |
    ⟨⟨hp, ho⟩, rfl⟩ | ⟨⟨hp, ho⟩, rfl⟩ | ⟨⟨hp, ho⟩, rfl⟩
  · exact .rdfs4a t.subject t.predicate t.object ht
  · exact .rdfs4b t.subject t.predicate t.object ht
  · exact .rdfs6 t.subject (by simpa only [← hp, ← ho] using ht)
  · exact .rdfs8 t.subject (by simpa only [← hp, ← ho] using ht)
  · exact .rdfs10 t.subject (by simpa only [← hp, ← ho] using ht)
  · exact .rdfs12 t.subject (by simpa only [← hp, ← ho] using ht)
  · exact .rdfs13 t.subject (by simpa only [← hp, ← ho] using ht)

theorem rdfsBinary_sound (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B) (t u q : GeneralizedTriple Iri Literal B)
    (ht : G t) (hu : G u) (hq : q ∈ rdfsBinary v t u) : RDFSStep T D v G q := by
  simp only [rdfsBinary, List.mem_append, mem_emit, or_assoc] at hq
  rcases hq with ⟨⟨hp, hj⟩, rfl⟩ | ⟨⟨hp, hj⟩, rfl⟩ | ⟨⟨hp, hq, hj⟩, rfl⟩ |
    ⟨⟨hp, hj⟩, rfl⟩ | ⟨⟨hp, hq, hj⟩, rfl⟩ | ⟨⟨hp, hq, hj⟩, rfl⟩
  · exact .rdfs2 t.subject t.object u.subject u.object
      (by simpa only [← hp] using ht) (by simpa only [← hj] using hu)
  · exact .rdfs3 t.subject t.object u.subject u.object
      (by simpa only [← hp] using ht) (by simpa only [← hj] using hu)
  · exact .rdfs5 t.subject t.object u.object
      (by simpa only [← hp] using ht) (by simpa only [hj, ← hq] using hu)
  · exact .rdfs7 t.subject t.object u.subject u.object
      (by simpa only [← hp] using ht) (by simpa only [← hj] using hu)
  · exact .rdfs9 t.subject t.object u.subject
      (by simpa only [← hp] using ht) (by simpa only [← hj, ← hq] using hu)
  · exact .rdfs11 t.subject t.object u.object
      (by simpa only [← hp] using ht) (by simpa only [hj, ← hq] using hu)

theorem rdfsNext_sound (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (xs : List (GeneralizedTriple Iri Literal B)) (q : GeneralizedTriple Iri Literal B)
    (hq : q ∈ rdfsNext v xs) : RDFSStep T v.toRDF.baseDatatypes v (Set.ofList xs) q := by
  simp only [rdfsNext, List.mem_append, or_assoc] at hq
  rcases hq with h | h | h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact .rdfs1 a (by simpa [RDFVocabulary.baseDatatypes, RDFSVocabulary.toRDF] using ha)
  · obtain ⟨t, ht, hq⟩ := List.mem_flatMap.mp h
    exact rdfsUnary_sound T _ v _ t q ht hq
  · obtain ⟨t, ht, hu⟩ := List.mem_flatMap.mp h
    obtain ⟨u, hu, hq⟩ := List.mem_flatMap.mp hu
    exact rdfsBinary_sound T _ v _ t u q ht hu hq

theorem rdfsNext_complete (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (xs : List (GeneralizedTriple Iri Literal B)) (q : GeneralizedTriple Iri Literal B)
    (h : RDFSStep T v.toRDF.baseDatatypes v (Set.ofList xs) q) : q ∈ rdfsNext v xs := by
  have zero (q) (hq : q ∈ rdfsZero v) : q ∈ rdfsNext v xs := by
    simp only [rdfsNext, List.mem_append]
    exact Or.inl (Or.inl hq)
  have unary (t q) (ht : t ∈ xs) (hq : q ∈ rdfsUnary v t) : q ∈ rdfsNext v xs := by
    simp only [rdfsNext, List.mem_append]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨t, ht, hq⟩))
  have binary (t u q) (ht : t ∈ xs) (hu : u ∈ xs) (hq : q ∈ rdfsBinary v t u) : q ∈ rdfsNext v xs := by
    simp only [rdfsNext, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨u, hu, hq⟩⟩)
  cases h with
  | rdfs1 a ha =>
    apply zero
    apply List.mem_map.mpr
    exact ⟨a, by simpa [RDFVocabulary.baseDatatypes, RDFSVocabulary.toRDF] using ha, rfl⟩
  | rdfs2 p c s o ht hu => exact binary _ _ _ ht hu (by simp [rdfsBinary, emit])
  | rdfs3 p c s o ht hu => exact binary _ _ _ ht hu (by simp [rdfsBinary, emit])
  | rdfs4a s p o ht => exact unary _ _ ht (by simp [rdfsUnary, emit])
  | rdfs4b s p o ht => exact unary _ _ ht (by simp [rdfsUnary, emit])
  | rdfs5 p q r ht hu => exact binary _ _ _ ht hu (by simp [rdfsBinary, emit])
  | rdfs6 p ht => exact unary _ _ ht (by simp [rdfsUnary, emit])
  | rdfs7 p q s o ht hu => exact binary _ _ _ ht hu (by simp [rdfsBinary, emit])
  | rdfs8 c ht => exact unary _ _ ht (by simp [rdfsUnary, emit])
  | rdfs9 c d x ht hu => exact binary _ _ _ ht hu (by simp [rdfsBinary, emit])
  | rdfs10 c ht => exact unary _ _ ht (by simp [rdfsUnary, emit])
  | rdfs11 c d e ht hu => exact binary _ _ _ ht hu (by simp [rdfsBinary, emit])
  | rdfs12 p ht => exact unary _ _ ht (by simp [rdfsUnary, emit])
  | rdfs13 c ht => exact unary _ _ ht (by simp [rdfsUnary, emit])

theorem rdfsNext_iff (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (xs : List (GeneralizedTriple Iri Literal B)) (q : GeneralizedTriple Iri Literal B) :
    q ∈ rdfsNext v xs ↔ RDFSStep T v.toRDF.baseDatatypes v (Set.ofList xs) q :=
  ⟨rdfsNext_sound T v xs q, rdfsNext_complete T v xs q⟩

def combinedNext (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (xs : List (GeneralizedTriple Iri Literal B)) : List (GeneralizedTriple Iri Literal B) :=
  rdfNext datatype v.toRDF xs ++ rdfsNext v xs

theorem combinedNext_iff (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (xs : List (GeneralizedTriple Iri Literal B)) (q : GeneralizedTriple Iri Literal B) :
    q ∈ combinedNext T.literalSyntax.datatype v xs ↔
      RDFSGeneralizedStep T v.toRDF.baseDatatypes v (Set.ofList xs) q := by
  rw [combinedNext, List.mem_append, rdfNext_iff T v.toRDF, rdfsNext_iff T v]
  rfl

omit [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B] in
theorem rdfStep_mono (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFVocabulary Iri)
    (G H : GeneralizedGraph Iri Literal B) (hGH : Set.subset G H)
    (t : GeneralizedTriple Iri Literal B) (h : RDFStep T D v G t) : RDFStep T D v H t := by
  cases h with
  | rdfD2 t ht => exact .rdfD2 t (hGH _ ht)
  | GrdfD1 s p l ht hd => exact .GrdfD1 s p l (hGH _ ht) hd

omit [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B] in
theorem rdfsStep_mono (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (G H : GeneralizedGraph Iri Literal B) (hGH : Set.subset G H)
    (t : GeneralizedTriple Iri Literal B) (h : RDFSStep T D v G t) : RDFSStep T D v H t := by
  cases h with
  | rdfs1 a ha => exact .rdfs1 a ha
  | rdfs2 p c s o h1 h2 => exact .rdfs2 p c s o (hGH _ h1) (hGH _ h2)
  | rdfs3 p c s o h1 h2 => exact .rdfs3 p c s o (hGH _ h1) (hGH _ h2)
  | rdfs4a s p o ht => exact .rdfs4a s p o (hGH _ ht)
  | rdfs4b s p o ht => exact .rdfs4b s p o (hGH _ ht)
  | rdfs5 p q r h1 h2 => exact .rdfs5 p q r (hGH _ h1) (hGH _ h2)
  | rdfs6 p ht => exact .rdfs6 p (hGH _ ht)
  | rdfs7 p q s o h1 h2 => exact .rdfs7 p q s o (hGH _ h1) (hGH _ h2)
  | rdfs8 c ht => exact .rdfs8 c (hGH _ ht)
  | rdfs9 c d x h1 h2 => exact .rdfs9 c d x (hGH _ h1) (hGH _ h2)
  | rdfs10 c ht => exact .rdfs10 c (hGH _ ht)
  | rdfs11 c d e h1 h2 => exact .rdfs11 c d e (hGH _ h1) (hGH _ h2)
  | rdfs12 p ht => exact .rdfs12 p (hGH _ ht)
  | rdfs13 c ht => exact .rdfs13 c (hGH _ ht)

omit [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B] in
theorem combinedStep_mono (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (G H : GeneralizedGraph Iri Literal B) (hGH : Set.subset G H)
    (t : GeneralizedTriple Iri Literal B) (h : RDFSGeneralizedStep T D v G t) :
    RDFSGeneralizedStep T D v H t :=
  h.elim (fun h => Or.inl (rdfStep_mono T D v.toRDF G H hGH t h))
    (fun h => Or.inr (rdfsStep_mono T D v G H hGH t h))

end RDF11.ClosureEvaluation
