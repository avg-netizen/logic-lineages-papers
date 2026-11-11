module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open OriginalHereditaryValidityInternalPushSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundSubst weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalRawSyntaxTransportInternalMachineCompletion OriginalRawSyntaxTransportInternalMachineCompletionSyntaxProof
open InternalStrongInduction
theorem atRawSubst {α β : Type} (mode : Mode) (payload : OTerm α) (ts : α → OTerm β) :
    (AtRaw mode payload).subst (fun a => emb (ts a)) =
      AtRaw mode (payload.subst ts) := by
  unfold AtRaw rawMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCompletionSubst,liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem atRawRename {α β : Type} (mode : Mode) (payload : OTerm α) (j : α → β) :
    (AtRaw mode payload).relabel j =
      AtRaw mode (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw mode payload).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]


theorem rawMatrixWitness {α : Type} (mode : Mode) (raw d k : OTerm α) :
    (rawMatrix mode raw).subst
      (Sum.elim Term.var (fun i => emb (![d,k] i))) =
      HasCompletion mode d k raw raw := by
  have he : (Sum.elim Term.var (fun i => emb (![d,k] i))) =
      (fun a => emb (Sum.elim Term.var ![d,k] a)) := by
    funext a
    cases a <;> rfl
  unfold rawMatrix
  rw [he]
  simp only [hasCompletionSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

def rawPredicate (mode : Mode) {α : Type} : Formula (α ⊕ Fin 1) :=
  AtRaw mode (.var (.inr 0))


def belowRaw {α : Type} (mode : Mode) (payload : OTerm α) : Formula α :=
  InternalStrongInduction.below (rawPredicate mode) payload


theorem rawPredicateInstantiate {α : Type} (mode : Mode) (payload : OTerm α) :
    instantiate (rawPredicate mode) (emb payload) =
      AtRaw mode payload := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]


@[simp] theorem belowRawRename {α β : Type} (mode : Mode) (payload : OTerm α) (j : α → β) :
    (belowRaw mode payload).relabel j =
      belowRaw mode (payload.relabel j) := by
  unfold belowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl


theorem rawPredicateLift {α : Type} (mode : Mode) :
    lift (rawPredicate mode (α := α)) =
      rawPredicate mode (α := α ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineCompletionRawSyntaxProof
