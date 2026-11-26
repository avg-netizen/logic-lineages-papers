module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.AllAcceptedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.SyntaxProof
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

theorem backClosedSubst {alpha beta : Type} (E : Program 3) (pool carrier parameter : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (forwardClosedAt R E pool carrier parameter).subst (fun a => emb (ts a)) =
 forwardClosedAt R E (pool.subst ts) (carrier.subst ts) (parameter.subst ts) := by
 unfold forwardClosedAt forwardMatrixAt forwardMatrix accepted
 rw [allBlockSubst,liftedEmbedding]
 simp only [accepted,impSubst,conjunctionSubst,graphOneSubst,graphTwoSubst,graphThreeSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem backClosedRename {alpha beta : Type} (E : Program 3) (pool carrier parameter : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
 (forwardClosedAt R E pool carrier parameter).relabel j = forwardClosedAt R E (pool.relabel j) (carrier.relabel j) (parameter.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (forwardClosedAt R E pool carrier parameter).subst (fun a => emb (.var (j a))) = _
 rw [backClosedSubst]
 simp only [← termRelabelAsSubst]
theorem backwardWitness {alpha : Type} (E : Program 3) (pool carrier parameter x y : OrdinaryArithmetic.Term alpha) :
 (forwardMatrixAt R E pool carrier parameter).subst (Sum.elim Term.var (fun i => emb (![x,y] i))) =
 (accepted R carrier x ⊓ graph3 E (numeral 1) x y parameter).imp (accepted R carrier y) := by
 have he : (Sum.elim Term.var (fun i => emb (![x,y] i))) = (fun a => emb (Sum.elim Term.var ![x,y] a)) := by
  funext a; cases a <;> rfl
 unfold forwardMatrixAt forwardMatrix accepted
 rw [he]
 simp only [accepted,impSubst,conjunctionSubst,graphOneSubst,graphTwoSubst,graphThreeSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl

@[simp] theorem scalarAcceptedRename (R : Program 1) {alpha beta : Type} (ref x : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
 (accepted R ref x).relabel j = accepted R (ref.relabel j) (x.relabel j) := by
 exact acceptedRename (R := R) ref ref ref x j
@[simp] theorem scalarAllAcceptedRename (R : Program 1) {alpha beta : Type} (ref reached : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
 (allAccepted R ref reached).relabel j = allAccepted R (ref.relabel j) (reached.relabel j) := by
 exact allAcceptedRename (R := R) ref ref ref reached j
@[simp] theorem forwardClosedRename (R : Program 1) (E : Program 3) {alpha beta : Type} (ref parameter : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
 (forwardClosed R E ref parameter).relabel j = forwardClosed R E (ref.relabel j) (parameter.relabel j) := by
 exact backClosedRename (R := R) E ref ref parameter j

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.SyntaxProof
