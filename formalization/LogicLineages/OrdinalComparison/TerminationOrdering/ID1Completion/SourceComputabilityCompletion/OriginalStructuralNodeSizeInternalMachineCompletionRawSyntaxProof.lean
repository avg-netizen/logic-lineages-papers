module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawSyntaxProof
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

open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open InternalStrongInduction
theorem atRawSubst {α β : Type} (payload : OTerm α) (ts : α → OTerm β) :
    (AtRaw payload).subst (fun a => emb (ts a)) =
      AtRaw (payload.subst ts) := by
  unfold AtRaw rawMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    hasCompletionSubst,liftSubst,Term.subst,Sum.elim_inr]


@[simp] theorem atRawRename {α β : Type} (payload : OTerm α) (j : α → β) :
    (AtRaw payload).relabel j =
      AtRaw (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw payload).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]


theorem rawMatrixWitness {α : Type} (raw d k : OTerm α) :
    (rawMatrix raw).subst
      (Sum.elim Term.var (fun i => emb (![d,k] i))) =
      HasCompletion d k raw raw := by
  have he : (Sum.elim Term.var (fun i => emb (![d,k] i))) =
      (fun a => emb (Sum.elim Term.var ![d,k] a)) := by
    funext a
    cases a <;> rfl
  unfold rawMatrix
  rw [he]
  simp only [hasCompletionSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

def rawPredicate {α : Type} : Formula (α ⊕ Fin 1) :=
  AtRaw (.var (.inr 0))


def belowRaw {α : Type} (payload : OTerm α) : Formula α :=
  InternalStrongInduction.below (rawPredicate) payload


theorem rawPredicateInstantiate {α : Type} (payload : OTerm α) :
    instantiate (rawPredicate) (emb payload) =
      AtRaw payload := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]


@[simp] theorem belowRawRename {α β : Type} (payload : OTerm α) (j : α → β) :
    (belowRaw payload).relabel j =
      belowRaw (payload.relabel j) := by
  unfold belowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl


theorem rawPredicateLift {α : Type} :
    lift (rawPredicate (α := α)) =
      rawPredicate (α := α ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRawSyntaxProof
