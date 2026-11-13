module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankCalibrationInductionDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

variable (R : Program 2) (H G : Program 1) (M W : Program 2)
theorem atRawSubst {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw R H G M W raw).subst (fun a => emb (ts a)) = AtRaw R H G M W (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,fields,graph1,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw R H G M W raw).relabel j = AtRaw R H G M W (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw R H G M W raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (input packed parameter rank : OTerm alpha) :
    (matrix R H G M W input).subst (Sum.elim Term.var (fun i => emb (![packed,parameter,rank] i))) =
      (fields R H G M W input packed parameter rank).imp (graph1 RankMemoDefinitions.decoder rank input) := by
  have he : (Sum.elim Term.var (fun i => emb (![packed,parameter,rank] i))) =
      (fun a => emb (Sum.elim Term.var ![packed,parameter,rank] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,graph1,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate R H G M W) (emb raw) = AtRaw R H G M W raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw R H G M W raw).relabel j = BelowRaw R H G M W (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type}  :
    lift (rawPredicate R H G M W (alpha := alpha)) = rawPredicate R H G M W (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionSyntaxProof
