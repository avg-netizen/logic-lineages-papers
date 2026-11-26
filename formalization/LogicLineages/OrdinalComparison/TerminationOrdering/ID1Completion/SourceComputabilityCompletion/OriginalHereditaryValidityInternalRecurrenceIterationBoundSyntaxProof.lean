module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb suc sucSubst sucRelabel bindEmbedding bindTerm nextEmbedding nextTerm)
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalAdditionLawsProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open SourceComputabilityFormulaSupportProof
open InternalClosedPrograms
open OriginalHereditaryValidityInternalPushSyntaxProof
open OriginalHereditaryValidityInternalRecurrence OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem weakBoundSubst {alpha beta : Type} (required count : OTerm alpha) (ts : alpha → OTerm beta) :
    (InternalPairingSumBounds.weakBound required count).subst (fun a => emb (ts a)) =
      InternalPairingSumBounds.weakBound (required.subst ts) (count.subst ts) := by
  change (ltF required (suc count)).subst (fun a => emb (ts a)) = ltF _ (suc _)
  simp only [orderSubst,sucSubst]

@[simp] theorem weakBoundRename {alpha beta : Type} (required count : OTerm alpha) (j : alpha → beta) :
    (InternalPairingSumBounds.weakBound required count).relabel j =
      InternalPairingSumBounds.weakBound (required.relabel j) (count.relabel j) := by
  change (ltF required (suc count)).relabel j = ltF _ (suc _)
  simp only [orderRename,sucRelabel]

/-- Numeric induction binds the entire arbitrary worklist and its actual
weight inside the row, so it applies to the changed successor worklist. -/
def sufficientBody {alpha : Type} (s t m : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (WorkFuelGraph (.var (.inr 1)) (.var (.inr 0)) ⊓
    InternalPairingSumBounds.weakBound (.var (.inr 1)) (count.relabel Sum.inl)).imp
      (TerminatedWork s t m (count.relabel Sum.inl) (.var (.inr 0)))

def sufficientRow {alpha : Type} (s t m : Program 2) (count : OTerm alpha) : Formula alpha :=
  allBlock (sufficientBody s t m count)

theorem sufficientRowSubst {alpha beta : Type} (s t m : Program 2)
    (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (sufficientRow s t m count).subst (fun a => emb (ts a)) = sufficientRow s t m (count.subst ts) := by
  unfold sufficientRow sufficientBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [workFuelSubst,weakBoundSubst,terminatedWorkSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem sufficientRowRename {alpha beta : Type} (s t m : Program 2)
    (count : OTerm alpha) (j : alpha → beta) :
    (sufficientRow s t m count).relabel j = sufficientRow s t m (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (sufficientRow s t m count).subst (fun a => emb (.var (j a))) = _
  rw [sufficientRowSubst]
  simp only [← termRelabelAsSubst]

theorem sufficientBodyWitness {alpha : Type} (s t m : Program 2)
    (count workCode required : OTerm alpha) :
    (sufficientBody s t m count).subst
      (Sum.elim Term.var (fun i => emb (![workCode,required] i))) =
      (WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required count).imp
        (TerminatedWork s t m count workCode) := by
  unfold sufficientBody
  rw [witnessEmbedding,impSubst,conjunctionSubst]
  simp only [workFuelSubst,weakBoundSubst,terminatedWorkSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem sufficientInstantiate {alpha : Type} (s t m : Program 2)
    (count : OTerm (alpha ⊕ Fin 1)) (v : OTerm alpha) :
    instantiate (sufficientRow s t m count) (emb v) =
      sufficientRow s t m (count.subst (bindTerm v)) := by
  rw [instantiate,bindEmbedding,sufficientRowSubst]

theorem sufficientSuccessor {alpha : Type} (s t m : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (sufficientRow s t m count) =
      sufficientRow s t m (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,sufficientRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof
