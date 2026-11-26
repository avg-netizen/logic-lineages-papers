module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.AllAcceptedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
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

theorem backClosedSubst {alpha beta : Type} (E : Program 3) (pool carrier parameter : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (backClosed E pool carrier parameter).subst (fun a => emb (ts a)) =
 backClosed E (pool.subst ts) (carrier.subst ts) (parameter.subst ts) := by
 unfold backClosed backwardMatrix
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,conjunctionSubst,graphTwoSubst,graphThreeSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem backClosedRename {alpha beta : Type} (E : Program 3) (pool carrier parameter : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
 (backClosed E pool carrier parameter).relabel j = backClosed E (pool.relabel j) (carrier.relabel j) (parameter.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (backClosed E pool carrier parameter).subst (fun a => emb (.var (j a))) = _
 rw [backClosedSubst]
 simp only [← termRelabelAsSubst]
theorem backwardWitness {alpha : Type} (E : Program 3) (pool carrier parameter x y : OrdinaryArithmetic.Term alpha) :
 (backwardMatrix E pool carrier parameter).subst (Sum.elim Term.var (fun i => emb (![x,y] i))) =
 (graph2 contains (numeral 1) pool x ⊓ (graph2 contains (numeral 1) carrier y ⊓ graph3 E (numeral 1) x y parameter)).imp
 (graph2 contains (numeral 1) carrier x) := by
 have he : (Sum.elim Term.var (fun i => emb (![x,y] i))) = (fun a => emb (Sum.elim Term.var ![x,y] a)) := by
  funext a; cases a <;> rfl
 unfold backwardMatrix
 rw [he]
 simp only [impSubst,conjunctionSubst,graphTwoSubst,graphThreeSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
