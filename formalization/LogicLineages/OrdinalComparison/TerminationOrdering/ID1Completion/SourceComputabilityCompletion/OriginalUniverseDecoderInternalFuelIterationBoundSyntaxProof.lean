module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundSyntaxProof
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
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuel (WorkFuelGraph)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof (workFuelSubst)
open OriginalTypedDecoderInternalFuelIterationBoundSyntaxProof (weakBoundSubst weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Numeric induction binds the entire arbitrary worklist and its actual
weight inside the row, so it applies to the changed successor worklist. -/
def sufficientBody {alpha : Type} (H : Program 1) (M contextWindow : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (WorkFuelGraph (.var (.inr 1)) (.var (.inr 0)) ⊓
    InternalPairingSumBounds.weakBound (.var (.inr 1)) (count.relabel Sum.inl)).imp
      (TerminatedWork H M contextWindow (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)))

def sufficientRow {alpha : Type} (H : Program 1) (M contextWindow : Program 2) (count : OTerm alpha) : Formula alpha :=
  allBlock (sufficientBody H M contextWindow count)

theorem sufficientRowSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (sufficientRow H M contextWindow count).subst (fun a => emb (ts a)) = sufficientRow H M contextWindow (count.subst ts) := by
  unfold sufficientRow sufficientBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [workFuelSubst,weakBoundSubst,terminatedWorkSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem sufficientRowRename {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm alpha) (j : alpha → beta) :
    (sufficientRow H M contextWindow count).relabel j = sufficientRow H M contextWindow (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (sufficientRow H M contextWindow count).subst (fun a => emb (.var (j a))) = _
  rw [sufficientRowSubst]
  simp only [← termRelabelAsSubst]

theorem sufficientBodyWitness {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode required c : OTerm alpha) :
    (sufficientBody H M contextWindow count).subst
      (Sum.elim Term.var (fun i => emb (![workCode,required,c] i))) =
      (WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required count).imp
        (TerminatedWork H M contextWindow count workCode c) := by
  unfold sufficientBody
  rw [witnessEmbedding,impSubst,conjunctionSubst]
  simp only [workFuelSubst,weakBoundSubst,terminatedWorkSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem sufficientInstantiate {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm (alpha ⊕ Fin 1)) (v : OTerm alpha) :
    instantiate (sufficientRow H M contextWindow count) (emb v) =
      sufficientRow H M contextWindow (count.subst (bindTerm v)) := by
  rw [instantiate,bindEmbedding,sufficientRowSubst]

theorem sufficientSuccessor {alpha : Type} (H : Program 1) (M contextWindow : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (sufficientRow H M contextWindow count) =
      sufficientRow H M contextWindow (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,sufficientRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundSyntaxProof
