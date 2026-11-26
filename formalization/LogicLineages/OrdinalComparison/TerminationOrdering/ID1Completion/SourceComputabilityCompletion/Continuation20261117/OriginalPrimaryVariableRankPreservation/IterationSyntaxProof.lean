module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {R : Program 1}

open Iteration SyntaxProof
theorem atCountSubst {alpha beta : Type} (E : Program 3)
 (count pool reached parameter carrier seed : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (AtCount R E count pool reached parameter carrier seed).subst (fun a => emb (ts a)) =
 AtCount R E (count.subst ts) (pool.subst ts) (reached.subst ts) (parameter.subst ts) (carrier.subst ts) (seed.subst ts) := by
 unfold AtCount matrix
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,allAcceptedSubst,graphFourSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (E : Program 3)
 (count pool reached parameter carrier seed : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
 (AtCount R E count pool reached parameter carrier seed).relabel j =
 AtCount R E (count.relabel j) (pool.relabel j) (reached.relabel j) (parameter.relabel j) (carrier.relabel j) (seed.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AtCount R E count pool reached parameter carrier seed).subst (fun a => emb (.var (j a))) = _
 rw [atCountSubst]
 simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type} (E : Program 3)
 (count pool reached parameter carrier seed out : OrdinaryArithmetic.Term alpha) :
 (matrix R E count pool reached parameter carrier seed).subst (Sum.elim Term.var (fun _ : Fin 1 => emb out)) =
 (graph4 (PrimaryIteration.iterate E) out count pool reached parameter).imp
 ((allAcceptedAt R pool carrier seed reached).imp (allAcceptedAt R pool carrier seed out)) := by
 have he : (Sum.elim Term.var (fun _ : Fin 1 => emb out)) = (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => out) a)) := by
  funext a; cases a <;> rfl
 unfold matrix
 rw [he]
 simp only [impSubst,allAcceptedSubst,graphFourSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationSyntaxProof
