module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionSyntaxProof
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
open EvaluatorConstructorInductionDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

open EvaluatorErasureSyntax
variable (R : Program 2) (H G : Program 1) (M W : Program 2)
theorem atLengthSubst {alpha beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (AtLength R H G M W count).subst (fun a => emb (ts a)) = AtLength R H G M W (count.subst ts) := by
 unfold AtLength applicationMatrix lambdaMatrix
 simp only [conjunctionSubst,allBlockSubst,liftedEmbedding]
 simp only [impSubst,applicationFields,lambdaFields,conjunctionSubst,
   InternalApplicationValidityClosure.applicationConstructors,OriginalContextInsertion.lengthGraph,
   admittedSubst,graph1,graph2,graph3,graph4,programSubst,numeral,zSubst,sucSubst,
   consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atLengthRename {alpha beta : Type} (count : OTerm alpha) (j : alpha → beta) :
 (AtLength R H G M W count).relabel j = AtLength R H G M W (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AtLength R H G M W count).subst (fun a => emb (.var (j a))) = _
 rw [atLengthSubst]
 simp only [← termRelabelAsSubst]
theorem predicateInstantiate {alpha : Type} (count : OTerm alpha) :
 instantiate (predicate R H G M W) (emb count) = AtLength R H G M W count := by
 rw [predicate,instantiate,bindEmbedding,atLengthSubst]
 simp only [varBind]
@[simp] theorem belowLengthRename {alpha beta : Type} (count : OTerm alpha) (j : alpha → beta) :
 (BelowLength R H G M W count).relabel j = BelowLength R H G M W (count.relabel j) := by
 unfold BelowLength
 rw [InternalStrongInductionSyntaxProof.belowRename]
 unfold predicate
 rw [atLengthRename]
 rfl
theorem predicateLift {alpha : Type} :
 lift (predicate R H G M W (alpha := alpha)) = predicate R H G M W (alpha := alpha ⊕ Fin 1) := by
 unfold lift predicate
 rw [atLengthRename]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionSyntaxProof
