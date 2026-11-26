module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceGenericSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceSyntaxProof
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
open EraseAbsence
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

attribute [local irreducible] programGraph

theorem resultSubst {alpha beta : Type} (raw needle bit : OTerm alpha) (ts : alpha → OTerm beta) :
    (result raw needle bit).subst (fun a => emb (ts a)) = result (raw.subst ts) (needle.subst ts) (bit.subst ts) := by
  exact EraseAbsenceGenericSyntaxProof.resultSubst ArgumentEntryCount.count raw needle bit ts

@[simp] theorem resultRename {alpha beta : Type} (raw needle bit : OTerm alpha) (j : alpha → beta) :
    (result raw needle bit).relabel j = result (raw.relabel j) (needle.relabel j) (bit.relabel j) := by
  exact EraseAbsenceGenericSyntaxProof.resultRename ArgumentEntryCount.count raw needle bit j

theorem atRawSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw raw).subst (fun a => emb (ts a)) = AtRaw (raw.subst ts) := by
  exact EraseAbsenceGenericSyntaxProof.atRawSubst ArgumentEntryCount.count Erase.state raw ts

@[simp] theorem atRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw raw).relabel j = AtRaw (raw.relabel j) := by
  exact EraseAbsenceGenericSyntaxProof.atRawRename ArgumentEntryCount.count Erase.state raw j

theorem matrixWitness {alpha : Type} (raw needle acc bit rest : OTerm alpha) :
    (matrix raw).subst (Sum.elim Term.var (fun i => emb (![needle,acc,bit,rest] i))) =
      (EraseInvariant.fields raw needle acc bit rest).imp (result raw needle bit) := by
  exact EraseAbsenceGenericSyntaxProof.matrixWitness ArgumentEntryCount.count Erase.state raw needle acc bit rest

theorem predicateInstantiate {alpha : Type} (raw : OTerm alpha) :
    instantiate (predicate) (emb raw) = AtRaw raw := by
  exact EraseAbsenceGenericSyntaxProof.predicateInstantiate ArgumentEntryCount.count Erase.state raw

@[simp] theorem belowRawRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw raw).relabel j = BelowRaw (raw.relabel j) := by
  exact EraseAbsenceGenericSyntaxProof.belowRawRename ArgumentEntryCount.count Erase.state raw j

theorem predicateLift {alpha : Type} :
    lift (predicate (alpha := alpha)) = predicate (alpha := alpha ⊕ Fin 1) := by
  exact EraseAbsenceGenericSyntaxProof.predicateLift ArgumentEntryCount.count Erase.state 

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceSyntaxProof
