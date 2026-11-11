module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalAbsorbProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalNumericIteration InternalNumericIterationSupportProof
open InternalNumericIterationFixedPointProof InternalNumericIterationFusionProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalNodeSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The unchanged iterator is the existing generic numeric repetition AST.
Failure absorption is internal and holds at every symbolic count. -/
theorem iterateFailure (s t m : Program 2) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma
      (graph2 (iterate s t m) (z : OTerm alpha) count z)) :=
  fixedValue (transition s t m) count z
    (OriginalHereditaryValidityInternalAbsorbProof.failureFixed s t m)

theorem iterateEmpty (s t m : Program 2) (count state : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateGraph state (numeral 1) z))) :
    Nonempty (Derivation body Gamma (graph2 (iterate s t m) state count state)) :=
  fixedValue (transition s t m) count state
    (OriginalHereditaryValidityInternalAbsorbProof.emptyFixed s t m state hs)

/-- Perform the FIRST transition, then the residual symbolic count.
Only internal numeric fusion and the original addition laws are used. -/
theorem iterateAfterFirst (s t m : Program 2) (count state next out : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph1 (transition s t m) next state)))
    (hr : Nonempty (Derivation body Gamma (graph2 (iterate s t m) out count next))) :
    Nonempty (Derivation body Gamma (graph2 (iterate s t m) out (suc count) state)) := by
  have hone := repeatSuccValue (transition s t m) z state next state
    (repeatZeroValue (transition s t m) state) hf
  have hsum := fusionValue (transition s t m) (suc z) count state next out hone hr
  have he : Derivation body Gamma (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  exact headTransport (iterate s t m) out (add (suc z) count) (suc count)
    (Fin.cons state Fin.elim0) ⟨he⟩ hsum

/-- Internal inverse of the same first-step decomposition; the given
first transition determines the residual run by Program functionality. -/
theorem iterateAfterFirstRecover (s t m : Program 2)
    (count state next out : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph1 (transition s t m) next state)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (iterate s t m) out (suc count) state))) :
    Nonempty (Derivation body Gamma (graph2 (iterate s t m) out count next)) := by
  have hone := repeatSuccValue (transition s t m) z state next state
    (repeatZeroValue (transition s t m) state) hf
  have he : Derivation body Gamma (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  have hsum := headTransport (iterate s t m) out (suc count) (add (suc z) count)
    (Fin.cons state Fin.elim0) ⟨symm he⟩ hr
  exact fusionRecover (transition s t m) (suc z) count state next out hone hsum

theorem rejectingFirstIterate (s t m : Program 2) (count state : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph1 (transition s t m) z state))) :
    Nonempty (Derivation body Gamma (graph2 (iterate s t m) z (suc count) state)) :=
  iterateAfterFirst s t m count state z z hf (iterateFailure s t m count)

/-- Literal failure cannot pass the ACTUAL finished AST. This uses its
status conjunct, not a native computation or a supplied terminal theorem. -/
theorem finishedFailureImpossible
    (h : Nonempty (Derivation body Gamma
      (graph1 finished (numeral 1) (z : OTerm alpha)))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons z Fin.elim0
  have ha := andLeft (conjunctionRecover (exactOne status)
    (InternalApplicationStepPeel.same work (InternalAcceptance.constantZero 1)) xs h)
  have hs := exactRecover status xs ha
  have hz : Nonempty (Derivation body Gamma (graph1 status (z : OTerm alpha) z)) :=
    pairLeft z z z OriginalHereditaryValidityInternalAbsorbProof.pairZero
  obtain ⟨he⟩ := valueUnique status (numeral 1) z xs hs hz
  exact ⟨sucNeZeroApply he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationProof
