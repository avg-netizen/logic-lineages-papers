module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
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
open Targets
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

theorem membersSubst {alpha beta : Type} (raw allowed : OTerm alpha) (ts : alpha → OTerm beta) :
    (allMembers raw allowed).subst (fun a => emb (ts a)) = allMembers (raw.subst ts) (allowed.subst ts) := by
  unfold allMembers memberMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph2,programSubst,OriginalTypedDecoderInternalLogicSyntaxProof.numeralSubst,numeral,zSubst,sucSubst,
    InternalLessThan.strictLess,orderSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem membersRename {alpha beta : Type} (raw allowed : OTerm alpha) (j : alpha → beta) :
    (allMembers raw allowed).relabel j = allMembers (raw.relabel j) (allowed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allMembers raw allowed).subst (fun a => emb (.var (j a))) = _
  rw [membersSubst]
  simp only [← termRelabelAsSubst]

theorem memberWitness {alpha : Type} (raw allowed key : OTerm alpha) :
    (memberMatrix raw allowed).subst (Sum.elim Term.var (fun _ : Fin 1 => emb key)) =
      (graph2 contains (numeral 1) raw key).imp (graph2 contains (numeral 1) allowed key) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb key)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => key) a)) := by
    funext a
    cases a <;> rfl
  unfold memberMatrix
  rw [he]
  simp only [impSubst,graph2,programSubst,OriginalTypedDecoderInternalLogicSyntaxProof.numeralSubst,numeral,zSubst,sucSubst,
    InternalLessThan.strictLess,orderSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
