module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.AcceptedSyntaxProof
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

theorem allAcceptedSubst {alpha beta : Type} (pool carrier seed reached : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
 (allAccepted pool carrier seed reached).subst (fun a => emb (ts a)) =
 allAccepted (pool.subst ts) (carrier.subst ts) (seed.subst ts) (reached.subst ts) := by
 unfold allAccepted memberAccepted
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,acceptedSubst,graphTwoSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem allAcceptedRename {alpha beta : Type} (pool carrier seed reached : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
 (allAccepted pool carrier seed reached).relabel j = allAccepted (pool.relabel j) (carrier.relabel j) (seed.relabel j) (reached.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (allAccepted pool carrier seed reached).subst (fun a => emb (.var (j a))) = _
 rw [allAcceptedSubst]
 simp only [← termRelabelAsSubst]
theorem memberWitness {alpha : Type} (pool carrier seed reached x : OrdinaryArithmetic.Term alpha) :
 (memberAccepted pool carrier seed reached).subst (Sum.elim Term.var (fun _ : Fin 1 => emb x)) =
 (graph2 contains (numeral 1) reached x).imp (accepted pool carrier seed x) := by
 have he : (Sum.elim Term.var (fun _ : Fin 1 => emb x)) = (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => x) a)) := by
  funext a; cases a <;> rfl
 unfold memberAccepted
 rw [he]
 simp only [impSubst,acceptedSubst,graphTwoSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SyntaxProof
