module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionInstancesProof
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

open EvaluatorErasureSyntax EvaluatorErasureDefinitions
open InternalApplicationStepPeelSupportProof (andLeft andRight)
variable (R : Program 2) (H G : Program 1) (M W : Program 2)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem applicationWitness (count : OTerm alpha) (xs : Fin 16 → OTerm alpha) :
 (applicationMatrix R H G M W count).subst (Sum.elim Term.var (fun i => emb (xs i))) =
 (applicationFields R H G M W count xs).imp (AdmittedPair R H G M W (xs 0) (xs 1) (xs 13)) := by
 have hh : (Sum.elim Term.var (fun i => emb (xs i))) =
   (fun a => emb (Sum.elim Term.var xs a)) := by
  funext a
  cases a <;> rfl
 unfold applicationMatrix applicationFields
 rw [hh]
 simp only [impSubst,conjunctionSubst,InternalApplicationValidityClosure.applicationConstructors,
   OriginalContextInsertion.lengthGraph,admittedSubst,graph1,graph2,graph3,graph4,
   programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
theorem applicationApply (count : OTerm alpha) (xs : Fin 16 → OTerm alpha)
 (h : Nonempty (Derivation body Delta (AtLength R H G M W count)))
 (hf : Nonempty (Derivation body Delta (applicationFields R H G M W count xs))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W (xs 0) (xs 1) (xs 13))) := by
 obtain ⟨hh⟩ := InternalClosedProgramsBindingProof.elimination body alpha 16 Delta
   (applicationMatrix R H G M W count) (fun i => emb (xs i)) (andLeft h)
 rw [applicationWitness] at hh
 exact ⟨Derivation.implicationElimination hh (Classical.choice hf)⟩
theorem lambdaWitness (count : OTerm alpha) (xs : Fin 11 → OTerm alpha) :
 (lambdaMatrix R H G M W count).subst (Sum.elim Term.var (fun i => emb (xs i))) =
 (lambdaFields R H G M W count xs).imp (AdmittedPair R H G M W (xs 0) (xs 1) (xs 6)) := by
 have hh : (Sum.elim Term.var (fun i => emb (xs i))) =
   (fun a => emb (Sum.elim Term.var xs a)) := by
  funext a
  cases a <;> rfl
 unfold lambdaMatrix lambdaFields
 rw [hh]
 simp only [impSubst,conjunctionSubst,InternalApplicationValidityClosure.applicationConstructors,
   OriginalContextInsertion.lengthGraph,admittedSubst,graph1,graph2,graph3,graph4,
   programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
theorem lambdaApply (count : OTerm alpha) (xs : Fin 11 → OTerm alpha)
 (h : Nonempty (Derivation body Delta (AtLength R H G M W count)))
 (hf : Nonempty (Derivation body Delta (lambdaFields R H G M W count xs))) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W (xs 0) (xs 1) (xs 6))) := by
 obtain ⟨hh⟩ := InternalClosedProgramsBindingProof.elimination body alpha 11 Delta
   (lambdaMatrix R H G M W count) (fun i => emb (xs i)) (andRight h)
 rw [lambdaWitness] at hh
 exact ⟨Derivation.implicationElimination hh (Classical.choice hf)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionInstancesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionInstancesProof
