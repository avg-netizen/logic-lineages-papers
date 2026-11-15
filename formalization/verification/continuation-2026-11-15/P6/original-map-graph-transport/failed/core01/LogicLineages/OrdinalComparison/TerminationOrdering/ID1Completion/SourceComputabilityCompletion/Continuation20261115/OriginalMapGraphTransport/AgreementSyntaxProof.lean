module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementSyntaxProof
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

theorem agreementSubst {alpha beta : Type} (keys left right : OTerm alpha) (ts : alpha → OTerm beta) :
    (lookupAgreement keys left right).subst (fun a => emb (ts a)) = lookupAgreement (keys.subst ts) (left.subst ts) (right.subst ts) := by
  unfold lookupAgreement agreementMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem agreementRename {alpha beta : Type} (keys left right : OTerm alpha) (j : alpha → beta) :
    (lookupAgreement keys left right).relabel j = lookupAgreement (keys.relabel j) (left.relabel j) (right.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (lookupAgreement keys left right).subst (fun a => emb (.var (j a))) = _
  rw [agreementSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (keys left right key value : OTerm alpha) :
    (agreementMatrix keys left right).subst (Sum.elim Term.var (fun i => emb (![key,value] i))) =
      (graph2 contains (numeral 1) keys key).imp
        ((graph2 ExchangeMapGraph.lookup value left key).imp (graph2 ExchangeMapGraph.lookup value right key)) := by
  have he : (Sum.elim Term.var (fun i => emb (![key,value] i))) =
      (fun a => emb (Sum.elim Term.var ![key,value] a)) := by
    funext a
    cases a <;> rfl
  unfold agreementMatrix
  rw [he]
  simp only [impSubst,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.AgreementSyntaxProof
