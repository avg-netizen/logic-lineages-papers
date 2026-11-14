module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldSyntaxProof
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
open Fold
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

variable {k : Nat} (base : Program k) (step : Program (k+2)) (transform : Program (k+1))
@[simp] theorem resultRename {alpha beta : Type} (out image : OTerm alpha) (j : alpha → beta) :
    (result out image).relabel j = result (out.relabel j) (image.relabel j) := by
  simp only [result,graph2,programRename,consTermRename,emptyRename,numeral,sucRelabel,zRelabel]

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw base step transform raw).subst (fun a => emb (ts a)) = AtRaw base step transform (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,fields,result,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw base step transform raw).relabel j = AtRaw base step transform (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw base step transform raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (raw needle image out : OTerm alpha) (params : Fin k → OTerm alpha) :
    (matrix base step transform raw).subst
      (Sum.elim Term.var (fun i => emb ((Fin.cons needle (Fin.cons image (Fin.cons out params)) : Fin (k+3) → OTerm alpha) i))) =
      (fields base step transform raw needle image out params).imp (result out image) := by
  have he : (Sum.elim Term.var (fun i => emb ((Fin.cons needle (Fin.cons image (Fin.cons out params)) : Fin (k+3) → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (Fin.cons needle (Fin.cons image (Fin.cons out params)) : Fin (k+3) → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,result,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr,Fin.cons_zero,Fin.cons_succ]
  rfl

theorem rawPredicateInstantiate {alpha : Type} (raw : OTerm alpha) :
    instantiate (rawPredicate base step transform) (emb raw) = AtRaw base step transform raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]
@[simp] theorem belowRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw base step transform raw).relabel j = BelowRaw base step transform (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl
theorem rawPredicateLift {alpha : Type} :
    lift (rawPredicate base step transform (alpha := alpha)) = rawPredicate base step transform (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldSyntaxProof
