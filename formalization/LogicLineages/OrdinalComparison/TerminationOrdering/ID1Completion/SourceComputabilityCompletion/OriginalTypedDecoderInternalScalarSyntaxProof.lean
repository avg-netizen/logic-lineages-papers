module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb sucSubst zSubst sucRelabel zRelabel bindEmbedding varBind liftBind)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepPairSubst {beta : Type} (code x y : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepPair code x y).subst (fun a => emb (ts a)) =
      StepPair (code.subst ts) (x.subst ts) (y.subst ts) := by
  simp only [StepPair,programSubst,Matrix.vecCons,Matrix.vecEmpty,consTermSubst,emptySubst]

@[simp] theorem stepPairRename {beta : Type} (code x y : OTerm alpha) (j : alpha → beta) :
    (StepPair code x y).relabel j =
      StepPair (code.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [StepPair,programRename,Matrix.vecCons,Matrix.vecEmpty,consTermRename,emptyRename]

theorem stepConsSubst {beta : Type} (code x y : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepCons code x y).subst (fun a => emb (ts a)) =
      StepCons (code.subst ts) (x.subst ts) (y.subst ts) := by
  simp only [StepCons,programSubst,Matrix.vecCons,Matrix.vecEmpty,consTermSubst,emptySubst]

@[simp] theorem stepConsRename {beta : Type} (code x y : OTerm alpha) (j : alpha → beta) :
    (StepCons code x y).relabel j =
      StepCons (code.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [StepCons,programRename,Matrix.vecCons,Matrix.vecEmpty,consTermRename,emptyRename]

theorem stepLiveSubst {beta : Type} (out work : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepLive out work).subst (fun a => emb (ts a)) =
      StepLive (out.subst ts) (work.subst ts) := by
  simp only [StepLive,stepPairSubst,numeral,sucSubst,zSubst]

@[simp] theorem stepLiveRename {beta : Type} (out work : OTerm alpha) (j : alpha → beta) :
    (StepLive out work).relabel j = StepLive (out.relabel j) (work.relabel j) := by
  simp only [StepLive,stepPairRename,numeral,sucRelabel,zRelabel]

theorem stepArrowFieldsSubst {beta : Type}
    (code domain codomain : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepArrowFields code domain codomain).subst (fun a => emb (ts a)) =
      StepArrowFields (code.subst ts) (domain.subst ts) (codomain.subst ts) := by
  unfold StepArrowFields
  rw [existsSubst,liftedEmbedding]
  simp only [conjunctionSubst,programSubst,Matrix.vecCons,Matrix.vecEmpty,consTermSubst,emptySubst,stepPairSubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem stepArrowFieldsRename {beta : Type}
    (code domain codomain : OTerm alpha) (j : alpha → beta) :
    (StepArrowFields code domain codomain).relabel j =
      StepArrowFields (code.relabel j) (domain.relabel j) (codomain.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepArrowFields code domain codomain).subst (fun a => emb (.var (j a))) = _
  rw [stepArrowFieldsSubst]
  simp only [← termRelabelAsSubst]

theorem stepArrowFieldsInstantiate (code domain codomain previous : OTerm alpha) :
    instantiate
      (programGraph InternalEqualityTest.predecessor (.var (.inr 0)) ![code.relabel Sum.inl] ⊓
        StepPair (.var (.inr 0)) (domain.relabel Sum.inl) (codomain.relabel Sum.inl))
      (emb previous) =
      graph1 InternalEqualityTest.predecessor previous code ⊓ StepPair previous domain codomain := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [programSubst,Matrix.vecCons,Matrix.vecEmpty,consTermSubst,emptySubst,stepPairSubst,varBind,liftBind]

theorem stepArrowFieldsIntro (code domain codomain previous : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalEqualityTest.predecessor previous code)))
    (hf : Nonempty (Derivation body Delta (StepPair previous domain codomain))) :
    Nonempty (Derivation body Delta (StepArrowFields code domain codomain)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hf⟩ := hf
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb previous)
  rw [stepArrowFieldsInstantiate]
  exact Derivation.conjunctionIntroduction hp hf

theorem stepArrowFieldsCases (code domain codomain : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (StepArrowFields code domain codomain)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (previous : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph1 InternalEqualityTest.predecessor previous (code.relabel j))) →
      Nonempty (Derivation body Theta
        (StepPair previous (domain.relabel j) (codomain.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  let P := graph1 InternalEqualityTest.predecessor (.var (.inr (0 : Fin 1)))
      (code.relabel Sum.inl) ⊓
    StepPair (.var (.inr 0)) (domain.relabel Sum.inl) (codomain.relabel Sum.inl)
  let Theta := P :: Delta.map weaken
  obtain ⟨d⟩ := k (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

/-- Ordinary arithmetic witnesses are embedded without changing their codes. -/
theorem witnessEmbedding {k : Nat} (ys : Fin k → OTerm alpha) :
    (Sum.elim Term.var (fun i => emb (ys i))) =
      (fun a => emb (Sum.elim Term.var ys a)) := by
  funext a
  cases a <;> rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
