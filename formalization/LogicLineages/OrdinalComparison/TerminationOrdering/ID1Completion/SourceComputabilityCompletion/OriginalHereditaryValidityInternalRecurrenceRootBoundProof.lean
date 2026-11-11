module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalSquareRootArithmeticSupportProof (orderLeft)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (fuelRename)
open OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
open OriginalHereditaryValidityInternalRecurrenceDecreaseProof
open OriginalHereditaryValidityInternalRecurrenceIterationDecreaseProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem liveFailureImpossible (state workCode : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) workCode)))
    (he : Nonempty (Derivation body Gamma (equal state z))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  have he' : Nonempty (Derivation body Gamma (eqn state z)) := by simpa only [equalEqn] using he
  have hone := headTransport status (numeral 1) state z Fin.elim0 he'
    (pairLeft state (numeral 1) workCode hs)
  have hzero : Nonempty (Derivation body Gamma (graph1 status (z : OTerm alpha) z)) :=
    pairLeft z z z OriginalHereditaryValidityInternalAbsorbProof.pairZero
  obtain ⟨hbad⟩ := valueUnique status (numeral 1) z (Fin.cons z Fin.elim0) hone hzero
  exact ⟨sucNeZeroApply hbad⟩

/-- The exact original parent payload pays the ENTIRE next live worklist.
Its weight is connected to the actual successor by the independent internal
decrease theorem; no child-success or residual-fuel premise is assumed. -/
theorem nextFuelBound (s t m : Program 2)
    (state workCode frame raw parameter payload next nextWork nextFuel : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition s t m) next state)))
    (hn : Nonempty (Derivation body Gamma (StateGraph next (numeral 1) nextWork)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph nextFuel nextWork))) :
    Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound nextFuel payload)) := by
  have hparent := singletonWeight workCode frame raw parameter payload
    (andLeft (andRight hs)) (andRight (andRight hs)) hp
  have hd := decreaseCore s t m state workCode frame raw parameter z (suc payload) next hs hparent ht
  apply decreasedCases next (suc payload) _ hd
  · intro Delta inc he
    obtain ⟨hfalse⟩ := liveFailureImpossible next nextWork (weakenProof hn inc) he
    exact ⟨Derivation.explosion hfalse⟩
  · intro beta j Delta actualWork actualFuel hj ha hw hless
    rw [weakBoundRename]
    simp only [sucRelabel] at hless
    have hn' := renameInto hn j Delta hj
    simp only [StateGraph,graph2Rename,oneRename] at hn'
    have hf' := renameInto hf j Delta hj
    rw [fuelRename] at hf'
    have hew := valueUnique work actualWork (nextWork.relabel j)
      (Fin.cons (next.relabel j) Fin.elim0)
      (pairRight (next.relabel j) (numeral 1) actualWork ha)
      (pairRight (next.relabel j) (numeral 1) (nextWork.relabel j) hn')
    have hactual := headTransport workFuel actualFuel actualWork (nextWork.relabel j) Fin.elim0 hew hw
    obtain ⟨hef⟩ := valueUnique workFuel actualFuel (nextFuel.relabel j)
      (Fin.cons (nextWork.relabel j) Fin.elim0) hactual hf'
    obtain ⟨hless⟩ := hless
    exact ⟨orderLeft (suc (payload.relabel j)) hef hless⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootBoundProof
