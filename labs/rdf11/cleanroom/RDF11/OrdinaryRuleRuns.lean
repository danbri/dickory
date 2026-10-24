/-
RDF 1.1 Semantics Appendix A's first, ordinary-syntax procedure.
The seed has NO rdf:_1 fallback. Runs retain the whole graph. Fresh allocation
for rdfD1 is an explicit sufficient operational policy, not a source-mandated
algorithm. This is finite-run semantics, not an executable saturation scheduler
or a termination assertion; existing-witness reuse needs its own certificate.
-/
import RDF11.EntailmentClosure

namespace RDF11

def GeneralizedTriple.Ordinary (t : GeneralizedTriple Iri Literal B) : Prop :=
  ∃ q : Triple Iri Literal B, q.generalize = t

def GeneralizedGraph.Ordinary (G : GeneralizedGraph Iri Literal B) : Prop :=
  ∀ t, G t → t.Ordinary

theorem Graph.generalize_ordinary (G : Graph Iri Literal B) : G.generalize.Ordinary :=
  fun _ ⟨q, _, hq⟩ => ⟨q, hq⟩

theorem rdf_axioms_ordinary (v : RDFVocabulary Iri) :
    (v.axioms : GeneralizedGraph Iri Literal B).Ordinary := by
  rintro t (⟨p, _, rfl⟩ | rfl)
  · exact ⟨⟨.iri (v.iri p), v.iri .rdfType, .iri (v.iri .rdfProperty)⟩, rfl⟩
  · exact ⟨⟨.iri (v.iri .rdfNil), v.iri .rdfType, .iri (v.iri .rdfList)⟩, rfl⟩

theorem rdfs_axioms_ordinary (v : RDFSVocabulary Iri) :
    (v.axioms : GeneralizedGraph Iri Literal B).Ordinary := by
  rintro t ⟨s, p, o, _, rfl⟩
  exact ⟨⟨.iri (v.iri s), v.iri p, .iri (v.iri o)⟩, rfl⟩

def OrdinaryAxiomSeed (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    GeneralizedGraph Iri Literal B₁ :=
  fun t => G t ∨ NonContainerAxioms datatype container axioms t ∨
    ConclusionAxioms datatype container axioms E t

theorem ordinaryAxiomSeed_subset (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    Set.subset (OrdinaryAxiomSeed datatype container axioms G E) (Set.union G axioms) := by
  rintro t (hg | ha | ⟨n, _, ha⟩)
  · exact Or.inl hg
  · exact Or.inr ha.1
  · exact Or.inr ha.1

def freshLiteralExpansion (v : RDFVocabulary Iri) (datatype : Iri)
    (H : GeneralizedGraph Iri Literal B) (s p : Term Iri Literal B) (b : B) :
    GeneralizedGraph Iri Literal B :=
  Set.union H (Set.union (Set.singleton ⟨s, p, .blank b⟩)
    (Set.singleton ⟨.blank b, .iri (v.iri .rdfType), .iri datatype⟩))

/-- Shared-assignment rules are filtered to ordinary conclusions; rdfD1 has
its own graph transition because its two conclusions share one fresh witness. -/
inductive OrdinaryStep (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri)
    (step : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop)
    (H : GeneralizedGraph Iri Literal B) : GeneralizedGraph Iri Literal B → Prop where
  | rule (t) : step H t → t.Ordinary → OrdinaryStep T D v step H (Set.union H (Set.singleton t))
  | rdfD1 (s p l b) : H ⟨s, p, .literal l⟩ → D (T.literalSyntax.datatype l) →
      ¬ H.hasBlank b → (GeneralizedTriple.mk s p (.literal l)).Ordinary →
      OrdinaryStep T D v step H (freshLiteralExpansion v (T.literalSyntax.datatype l) H s p b)

inductive OrdinaryRun (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri)
    (step : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop)
    (seed : GeneralizedGraph Iri Literal B) : GeneralizedGraph Iri Literal B → Prop where
  | start : OrdinaryRun T D v step seed seed
  | next : OrdinaryRun T D v step seed H → OrdinaryStep T D v step H K →
      OrdinaryRun T D v step seed K

theorem OrdinaryStep.contains (h : OrdinaryStep T D v step H K) : Set.subset H K := by
  cases h <;> exact fun _ ht => Or.inl ht

theorem OrdinaryRun.contains (h : OrdinaryRun T D v step seed H) : Set.subset seed H := by
  induction h with
  | start => exact fun _ ht => ht
  | next _ hs ih => exact fun _ ht => hs.contains _ (ih _ ht)

theorem OrdinaryStep.ordinary (h : OrdinaryStep T D v step H K)
    (hH : H.Ordinary) : K.Ordinary := by
  cases h with
  | rule t _ ho =>
    rintro q (hq | rfl)
    · exact hH q hq
    · exact ho
  | rdfD1 s p l b _ _ _ ho =>
    obtain ⟨⟨s', p', o'⟩, he⟩ := ho
    have hs : s'.toTerm = s := congrArg GeneralizedTriple.subject he
    have hp : Term.iri p' = p := congrArg GeneralizedTriple.predicate he
    rintro q (hq | rfl | rfl)
    · exact hH q hq
    · exact ⟨⟨s', p', .blank b⟩, by simp [Triple.generalize, hs, hp]⟩
    · exact ⟨⟨.blank b, v.iri .rdfType, .iri (T.literalSyntax.datatype l)⟩, rfl⟩

theorem OrdinaryRun.ordinary (h : OrdinaryRun T D v step seed H)
    (hs : seed.Ordinary) : H.Ordinary := by
  induction h with
  | start => exact hs
  | next _ ht ih => exact ht.ordinary ih

/-- Omitting shared-assignment rules embeds every remaining run into the
larger strategy. This makes no quantitative claim about practical usefulness. -/
theorem OrdinaryStep.rules_mono
    {step₁ step₂ : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop}
    (hsub : ∀ H t, step₁ H t → step₂ H t) (h : OrdinaryStep T D v step₁ H K) :
    OrdinaryStep T D v step₂ H K := by
  cases h with
  | rule t ht ho => exact .rule t (hsub _ t ht) ho
  | rdfD1 s p l b ht hd hf ho => exact .rdfD1 s p l b ht hd hf ho

theorem OrdinaryRun.rules_mono
    {step₁ step₂ : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop}
    (hsub : ∀ H t, step₁ H t → step₂ H t) (h : OrdinaryRun T D v step₁ seed H) :
    OrdinaryRun T D v step₂ seed H := by
  induction h with
  | start => exact .start
  | next _ ht ih => exact .next ih (ht.rules_mono hsub)

namespace SimpleInterpretation

theorem freshLiteralExpansion_satisfaction (I : SimpleInterpretation Iri Literal U)
    (hI : I.RDFConditions T D v ρ) (H : GeneralizedGraph Iri Literal B)
    (s p : Term Iri Literal B) (l : Literal) (b : B)
    (ht : H ⟨s, p, .literal l⟩) (hd : D (T.literalSyntax.datatype l))
    (hf : ¬ H.hasBlank b) :
    I.Satisfies (freshLiteralExpansion v (T.literalSyntax.datatype l) H s p b) ↔ I.Satisfies H := by
  constructor
  · exact I.satisfies_subgraph (fun _ ht => Or.inl ht)
  · intro hH
    classical
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue H).mp hH
    obtain ⟨q, x, r, hp, hs, hl, hr⟩ := hA _ ht
    have hil : I.IL l = some r := by
      cases hv : I.IL l with
      | none => simp [denote, hv] at hl
      | some r' =>
        have he : r'.val = r.val := by simpa [denote, hv] using hl
        exact congrArg some (Subtype.ext he)
    let A' : I.Assignment B := fun c => if c = b then some r else A c
    have old : I.GraphTrue A' H := by
      intro t ht'
      apply (I.tripleTrue_agrees t (A := A) (B := A') ?_).mp (hA t ht')
      intro c hc
      have hn : c ≠ b := fun he => hf (he ▸ ⟨t, ht', hc⟩)
      simp [A', hn]
    obtain ⟨q', x', r', hp', hs', hl', hr'⟩ := old _ ht
    have he : r'.val = r.val := by simpa [denote, hil] using hl'.symm
    have he' : r' = r := Subtype.ext he
    subst r'
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A', ?_⟩
    rintro t (ht' | rfl | rfl)
    · exact old t ht'
    · exact ⟨q', x', r, hp', hs', by simp [denote, A'], hr'⟩
    · apply I.tripleTrue_of_relates A' _ (s := r.val) rfl (by simp [denote, A']) rfl
      exact I.rdf_literal_typing hI hd r hil

theorem ordinaryStep_satisfaction (I : SimpleInterpretation Iri Literal U)
    (hI : I.RDFConditions T D v ρ)
    (sound : ∀ H t (A : I.Assignment B), I.GraphTrue A H → step H t → I.TripleTrue A t)
    (h : OrdinaryStep T D v step H K) : I.Satisfies K ↔ I.Satisfies H := by
  cases h with
  | rule t ht _ =>
    constructor
    · exact I.satisfies_subgraph (fun _ h => Or.inl h)
    · intro hH
      obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue H).mp hH
      apply (I.satisfies_iff_exists_graphTrue _).mpr
      refine ⟨A, ?_⟩
      rintro q (hq | rfl)
      · exact hA q hq
      · exact sound H _ A hA ht
  | rdfD1 s p l b ht hd hf _ => exact I.freshLiteralExpansion_satisfaction hI H s p l b ht hd hf

theorem ordinaryRun_satisfaction (I : SimpleInterpretation Iri Literal U)
    (hI : I.RDFConditions T D v ρ)
    (sound : ∀ H t (A : I.Assignment B), I.GraphTrue A H → step H t → I.TripleTrue A t)
    (h : OrdinaryRun T D v step seed H) : I.Satisfies H ↔ I.Satisfies seed := by
  induction h with
  | start => rfl
  | next _ hs ih => exact (I.ordinaryStep_satisfaction hI sound hs).trans ih

theorem ordinaryAxiomSeed_satisfaction (I : SimpleInterpretation Iri Literal U)
    (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (ha : ∀ A : I.Assignment B₁, I.GraphTrue A axioms) :
    I.Satisfies (OrdinaryAxiomSeed datatype container axioms G E) ↔ I.Satisfies G := by
  constructor
  · exact I.satisfies_subgraph (fun _ ht => Or.inl ht)
  · intro hG
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, fun t ht => ?_⟩
    exact (ordinaryAxiomSeed_subset datatype container axioms G E t ht).elim (hA t) (ha A t)

end SimpleInterpretation

def OrdinaryRDFRun (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :=
  OrdinaryRun T v.baseDatatypes v (RDFStep T v.baseDatatypes v)
    (OrdinaryAxiomSeed T.literalSyntax.datatype (fun n => v.iri (.container n)) v.axioms G E)

def OrdinaryRDFSRun (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :=
  OrdinaryRun T v.toRDF.baseDatatypes v.toRDF (RDFSGeneralizedStep T v.toRDF.baseDatatypes v)
    (OrdinaryAxiomSeed T.literalSyntax.datatype (fun n => v.iri (.rdf (.container n)))
      (Set.union v.toRDF.axioms v.axioms) G E)

theorem ordinary_rdf_run_ordinary (run : OrdinaryRDFRun T v G E H) (hG : G.Ordinary) :
    H.Ordinary := by
  apply run.ordinary
  intro t ht
  exact (ordinaryAxiomSeed_subset _ _ _ _ _ t ht).elim (hG t) (rdf_axioms_ordinary v t)

theorem ordinary_rdfs_run_ordinary (run : OrdinaryRDFSRun T v G E H) (hG : G.Ordinary) :
    H.Ordinary := by
  apply run.ordinary
  intro t ht
  exact (ordinaryAxiomSeed_subset _ _ _ _ _ t ht).elim (hG t)
    (fun ha => ha.elim (rdf_axioms_ordinary v.toRDF t) (rdfs_axioms_ordinary v t))

theorem ordinary_rdf_run_satisfaction (I : SimpleInterpretation Iri Literal U)
    (hI : I.RDFModel T v.baseDatatypes v) (h : OrdinaryRDFRun T v G E H) :
    I.Satisfies H ↔ I.Satisfies G := by
  obtain ⟨ρ, hρ⟩ := hI
  exact (I.ordinaryRun_satisfaction hρ (fun _ _ A hH hs => I.rdf_step_sound hρ A hH hs) h).trans
    (I.ordinaryAxiomSeed_satisfaction _ _ _ G E (fun A t ht => I.rdf_axiom_true hρ A t ht))

theorem ordinary_rdfs_run_satisfaction (I : SimpleInterpretation Iri Literal U)
    (hI : I.RDFSModel T v.toRDF.baseDatatypes v) (h : OrdinaryRDFSRun T v G E H) :
    I.Satisfies H ↔ I.Satisfies G := by
  obtain ⟨ρ, hρ⟩ := hI
  exact (I.ordinaryRun_satisfaction hρ.rdf
    (fun _ _ A hH hs => I.rdfs_generalized_step_sound hρ A hH hs) h).trans
    (I.ordinaryAxiomSeed_satisfaction _ _ _ G E
      (fun A t ht => ht.elim (I.rdf_axiom_true hρ.rdf A t) (I.rdfs_axiom_true hρ A t)))

theorem ordinary_rdf_check_sound {G E H : GeneralizedGraph Iri Literal B}
    (run : OrdinaryRDFRun T v G E H)
    (μ : Substitution Iri Literal B) (check : Set.subset (E.substitute μ) H) :
    RDFEntails.{u} T v.baseDatatypes v G E := by
  intro U I hI hG
  have hH := (ordinary_rdf_run_satisfaction I hI run).mpr hG
  obtain ⟨ρ, hρ⟩ := hI
  exact rdf_condition_substitution_entails _ _ E μ U I hρ.property (I.satisfies_subgraph check hH)

theorem ordinary_rdfs_check_sound {G E H : GeneralizedGraph Iri Literal B}
    (run : OrdinaryRDFSRun T v G E H)
    (μ : Substitution Iri Literal B) (check : Set.subset (E.substitute μ) H) :
    RDFSEntails.{u} T v.toRDF.baseDatatypes v G E := by
  intro U I hI hG
  have hH := (ordinary_rdfs_run_satisfaction I hI run).mpr hG
  obtain ⟨ρ, hρ⟩ := hI
  exact rdf_condition_substitution_entails _ _ E μ U I hρ.rdf.property (I.satisfies_subgraph check hH)

end RDF11
