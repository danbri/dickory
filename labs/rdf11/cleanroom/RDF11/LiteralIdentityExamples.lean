/-
Consequences of RDF 1.1's characterwise literal identity and lowercase
language values. Symbolic IRI names are used; no IRI parser is claimed.
The example connects syntax, simple entailment, datatype equivalence and
the duplicate-free enumeration contract.
-/
import RDF11.StructuredLiterals
import RDF11.Interpolation
import RDF11.EnumerationImages

namespace RDF11.LiteralIdentity

abbrev Literal := StructuredLiteral RDFSymbol .rdfLangString

theorem lower_fr : asciiLower "fr" = "fr" := by
  simp only [asciiLower, String.map_eq_internal]
  decide

theorem lower_FR : asciiLower "FR" = "fr" := by
  simp only [asciiLower, String.map_eq_internal]
  decide

theorem wellFormed_fr : BCP47.WellFormed "fr" := by
  apply BCP47.wellFormed_of_primary
  rw [lower_fr]
  unfold BCP47.subtag BCP47.alpha
  decide

theorem all_grandfathered_wellFormed : ∀ s ∈ BCP47.grandfathered, BCP47.WellFormed s := by
  have hn : ∀ s ∈ BCP47.grandfathered, asciiLower s = s := by
    unfold BCP47.grandfathered
    simp only [asciiLower, String.map_eq_internal]
    decide +kernel
  intro s hs
  apply BCP47.wellFormed_grandfathered
  rw [hn s hs]
  exact hs

theorem uppercase_grandfathered : BCP47.WellFormed "I-AMI" := by
  apply BCP47.wellFormed_grandfathered
  simp only [asciiLower, String.map_eq_internal]
  unfold BCP47.grandfathered
  decide +kernel

theorem privateuse_wellFormed : BCP47.WellFormed "x-private" := by
  simp only [BCP47.WellFormed, asciiLower, String.map_eq_internal]
  change BCP47.languageTag ["x", "private"]
  refine Or.inr (Or.inl ⟨["private"], rfl, by decide, ?_⟩)
  unfold BCP47.subtags BCP47.subtag BCP47.alphanum BCP47.alpha BCP47.digit
  decide +kernel

theorem duplicate_variant_wellFormed : BCP47.WellFormed "de-1901-1901" := by
  simp only [BCP47.WellFormed, asciiLower, String.map_eq_internal]
  change BCP47.languageTag ["de", "1901", "1901"]
  have hv : BCP47.variant "1901" := by
    refine Or.inr ⟨?_, '1', ['9', '0', '1'], rfl, ?_⟩ <;>
      simp only [BCP47.subtag, BCP47.alphanum, BCP47.alpha, BCP47.digit] <;> decide +kernel
  refine Or.inl ⟨["de"], [], [], ["1901", "1901"], [], [], ?_, Or.inl rfl,
    Or.inl rfl, ?_, ?_, Or.inl rfl, rfl⟩
  · refine Or.inl ⟨"de", [], rfl, ?_, by decide, ?_⟩ <;>
      simp only [BCP47.subtags, BCP47.subtag, BCP47.alpha] <;> decide +kernel
  · simpa using hv
  · simp

def lowerTag : BCP47.Tag := ⟨"fr", wellFormed_fr⟩

def upperTag : BCP47.Tag :=
  ⟨"FR", (BCP47.wellFormed_of_lower_eq (lower_FR.trans lower_fr.symm)).mpr wellFormed_fr⟩

def lowerLiteral : Literal := .tagged "chat" lowerTag

def upperLiteral : Literal := .tagged "chat" upperTag

theorem literals_distinct : upperLiteral ≠ lowerLiteral := by
  intro h
  have ht := congrArg StructuredLiteral.language h
  exact (by decide : some "FR" ≠ some "fr") ht

theorem normalize_upper : upperLiteral.normalize = lowerLiteral := by
  apply (StructuredLiteral.eq_iff_fields _ _).mpr
  exact ⟨rfl, rfl, congrArg some lower_FR⟩

theorem normalize_lower : lowerLiteral.normalize = lowerLiteral := by
  apply (StructuredLiteral.eq_iff_fields _ _).mpr
  exact ⟨rfl, rfl, congrArg some lower_fr⟩

def edge (l : Literal) : GeneralizedTriple RDFSymbol Literal Empty :=
  ⟨.iri .rdfNil, .iri .rdfValue, .literal l⟩

theorem edge_injective (h : edge l = edge k) : l = k :=
  Term.literal.inj (congrArg GeneralizedTriple.object h)

theorem normalize_edge (l : Literal) :
    (edge l).mapLiteral StructuredLiteral.normalize = edge l.normalize := rfl

def original : GeneralizedGraph RDFSymbol Literal Empty :=
  Set.ofList [edge upperLiteral, edge lowerLiteral]

theorem normalized_graph :
    original.mapLiteral StructuredLiteral.normalize = Set.ofList [edge lowerLiteral] := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨u, hu, rfl⟩
    change u ∈ [edge upperLiteral, edge lowerLiteral] at hu
    rcases List.mem_cons.mp hu with he | he
    · subst u
      simp only [normalize_edge, normalize_upper]
      exact List.mem_cons_self
    · have hu : u = edge lowerLiteral := List.mem_singleton.mp he
      subst u
      simp only [normalize_edge, normalize_lower]
      exact List.mem_cons_self
  · intro ht
    have he : t = edge lowerLiteral := List.mem_singleton.mp ht
    subst t
    exact ⟨edge lowerLiteral, List.mem_cons_of_mem _ List.mem_cons_self,
      (normalize_edge lowerLiteral).trans (congrArg edge normalize_lower)⟩

def originalEnumeration : Enumeration original :=
  Enumeration.fromList [edge upperLiteral, edge lowerLiteral]

def normalizedEnumeration : Enumeration (original.mapLiteral StructuredLiteral.normalize) :=
  originalEnumeration.imageDeduplicated (GeneralizedTriple.mapLiteral StructuredLiteral.normalize)

theorem original_count : originalEnumeration.triples.length = 2 := by decide

theorem normalized_count : normalizedEnumeration.triples.length = 1 := by
  let other : Enumeration (original.mapLiteral StructuredLiteral.normalize) :=
    normalized_graph.symm ▸ Enumeration.fromList [edge lowerLiteral]
  have he := Enumeration.length_independent normalizedEnumeration other
  have ho := Enumeration.transport_length normalized_graph.symm
    (Enumeration.fromList [edge lowerLiteral])
  exact he.trans (ho.trans (by decide))

theorem case_change_not_simple_entailment :
    ¬ SimplyEntails.{u} (Set.ofList [edge upperLiteral]) (Set.ofList [edge lowerLiteral]) := by
  intro h
  have hg : GeneralizedGraph.ground (Set.ofList [edge lowerLiteral]) := fun b => nomatch b
  have hs := (ground_entailment_iff_subset _ _ hg).mp h
  have he : edge lowerLiteral = edge upperLiteral := List.mem_singleton.mp (hs _ List.mem_cons_self)
  exact literals_distinct (edge_injective he).symm

theorem case_change_d_equivalent (T : DatatypeTheory RDFSymbol Literal Value)
    (hs : T.literalSyntax = StructuredLiteral.literalSyntax RDFSymbol.rdfLangString)
    (D : Set RDFSymbol) (hd : D .rdfLangString) :
    DEntails.{u} T D (Set.ofList [edge upperLiteral]) (Set.ofList [edge lowerLiteral]) ∧
    DEntails.{u} T D (Set.ofList [edge lowerLiteral]) (Set.ofList [edge upperLiteral]) := by
  have h := StructuredLiteral.normalize_d_equivalent T hs D hd (Set.ofList [edge upperLiteral])
  simpa only [GeneralizedGraph.mapLiteral, Set.image_ofList, List.map_cons, List.map_nil,
    normalize_edge, normalize_upper] using h

end RDF11.LiteralIdentity
