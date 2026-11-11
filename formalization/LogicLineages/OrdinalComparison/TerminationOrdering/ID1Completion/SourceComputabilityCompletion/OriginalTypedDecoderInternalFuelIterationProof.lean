module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalNumericIteration InternalNumericIterationSupportProof
open InternalNumericIterationFixedPointProof InternalNumericIterationFusionProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalBranchProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Only arithmetic pair facts are reused from the earlier machine. The
fixed-point proofs below unfold the actual ORIGINAL typed transition. -/
theorem failureFixed (H : Program 1) :
    Nonempty (Derivation body Gamma (graph1 (transition H) (z : OTerm alpha) z)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons z Fin.elim0
  have hs : Nonempty (Derivation body Gamma (graph1 status (z : OTerm alpha) z)) :=
    pairLeft z z z InternalApplicationValidityStackAppendTransitionProof.pairZero
  have hn : Nonempty (Derivation body Gamma (equal (z : OTerm alpha) (numeral 1)).not) := by
    have he : Derivation body (equal (z : OTerm alpha) (numeral 1) :: Gamma)
        (eqn z (suc z)) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply (symm he))⟩
  exact sameNoIntro status (constant 1 1) _ (constant 1 0) z z (numeral 1) xs
    hs (constantValue 1 xs) hn (constantValue 0 xs)

theorem emptyFixed (H : Program 1) (state : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (StepLive state z))) :
    Nonempty (Derivation body Gamma (graph1 (transition H) state state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have he : Nonempty (Derivation body Gamma (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  apply sameYesIntro status (constant 1 1) _ (constant 1 0) state (numeral 1) (numeral 1) xs
    (pairLeft state (numeral 1) z h) (constantValue 1 xs) he
  exact InternalAcceptanceBranchProof.zeroBranchIntro work _ _ state xs
    (pairRight state (numeral 1) z h) (projectionValue 0 xs)

theorem iterateFailure (H : Program 1) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma (graph2 (iterate H) (z : OTerm alpha) count z)) :=
  fixedValue (transition H) count z (failureFixed H)

theorem iterateEmpty (H : Program 1) (count state : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state z))) :
    Nonempty (Derivation body Gamma (graph2 (iterate H) state count state)) :=
  fixedValue (transition H) count state (emptyFixed H state hs)

theorem iterateAfterFirst (H : Program 1) (count state next out : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph1 (transition H) next state)))
    (hr : Nonempty (Derivation body Gamma (graph2 (iterate H) out count next))) :
    Nonempty (Derivation body Gamma (graph2 (iterate H) out (suc count) state)) := by
  have hone := repeatSuccValue (transition H) z state next state
    (repeatZeroValue (transition H) state) hf
  have hsum := fusionValue (transition H) (suc z) count state next out hone hr
  have he : Derivation body Gamma (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  exact headTransport (iterate H) out (add (suc z) count) (suc count)
    (Fin.cons state Fin.elim0) ⟨he⟩ hsum

theorem iterateAfterFirstRecover (H : Program 1) (count state next out : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph1 (transition H) next state)))
    (hr : Nonempty (Derivation body Gamma (graph2 (iterate H) out (suc count) state))) :
    Nonempty (Derivation body Gamma (graph2 (iterate H) out count next)) := by
  have hone := repeatSuccValue (transition H) z state next state
    (repeatZeroValue (transition H) state) hf
  have he : Derivation body Gamma (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  have hsum := headTransport (iterate H) out (suc count) (add (suc z) count)
    (Fin.cons state Fin.elim0) ⟨symm he⟩ hr
  exact fusionRecover (transition H) (suc z) count state next out hone hsum

theorem rejectingFirstIterate (H : Program 1) (count state : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph1 (transition H) z state))) :
    Nonempty (Derivation body Gamma (graph2 (iterate H) z (suc count) state)) :=
  iterateAfterFirst H count state z z hf (iterateFailure H count)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationProof
