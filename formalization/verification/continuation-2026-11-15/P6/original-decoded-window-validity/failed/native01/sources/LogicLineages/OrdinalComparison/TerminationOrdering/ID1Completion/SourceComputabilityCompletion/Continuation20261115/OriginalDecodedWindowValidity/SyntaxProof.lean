module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.SyntaxProof
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

theorem membersSubst {alpha beta : Type} (n : Nat) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (boundedMembers n raw).subst (fun a => emb (ts a)) = boundedMembers n (raw.subst ts) := by
  unfold boundedMembers memberMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    InternalLessThan.strictLess,orderSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem membersRename {alpha beta : Type} (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (boundedMembers n raw).relabel j = boundedMembers n (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (boundedMembers n raw).subst (fun a => emb (.var (j a))) = _
  rw [membersSubst]
  simp only [← termRelabelAsSubst]

theorem memberWitness {alpha : Type} (n : Nat) (raw key : OTerm alpha) :
    (memberMatrix n raw).subst (Sum.elim Term.var (fun _ : Fin 1 => emb key)) =
      (graph2 contains (numeral 1) raw key).imp (InternalLessThan.strictLess key (numeral n)) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb key)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => key) a)) := by
    funext a
    cases a <;> rfl
  unfold memberMatrix
  rw [he]
  simp only [impSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    InternalLessThan.strictLess,orderSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.SyntaxProof
