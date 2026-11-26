module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFixedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification
open OriginalUniverseDecoderInternalFuelStepProof
open OriginalUniverseDecoderInternalFuelNumericSyntaxProof
open OriginalUniverseDecoderInternalFuelNumericSupportProof
open OriginalUniverseDecoderInternalFuelNumericFixedProof
open OriginalUniverseDecoderInternalFuelNumericFusionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem iterateFailure (H : Program 1) (M contextWindow : Program 2) (count c : OTerm alpha) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) z count z c)) :=
  fixedValue (transition H M contextWindow) count z c (failureFixed H M contextWindow c)

theorem iterateEmpty (H : Program 1) (M contextWindow : Program 2) (count state c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state z))) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) state count state c)) :=
  fixedValue (transition H M contextWindow) count state c (emptyFixed H M contextWindow state c hs)

theorem iterateAfterFirst (H : Program 1) (M contextWindow : Program 2)
    (count state next out c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph2 (transition H M contextWindow) next state c)))
    (hr : Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) out count next c))) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) out (suc count) state c)) := by
  have hone := repeatSuccValue (transition H M contextWindow) z state next state c
    (repeatZeroValue (transition H M contextWindow) state c) hf
  have hsum := fusionValue (transition H M contextWindow) (suc z) count state next out c hone hr
  have he : Derivation body Gamma (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  exact headTransport (iterate H M contextWindow) out (add (suc z) count) (suc count)
    ![state,c] ⟨he⟩ hsum

theorem iterateAfterFirstRecover (H : Program 1) (M contextWindow : Program 2)
    (count state next out c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph2 (transition H M contextWindow) next state c)))
    (hr : Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) out (suc count) state c))) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) out count next c)) := by
  have hone := repeatSuccValue (transition H M contextWindow) z state next state c
    (repeatZeroValue (transition H M contextWindow) state c) hf
  have he : Derivation body Gamma (eqn (add (suc z) count) (suc count)) :=
    trans (leftSuccessor z count) (congSuc (leftZero count))
  have hsum := headTransport (iterate H M contextWindow) out (suc count) (add (suc z) count)
    ![state,c] ⟨symm he⟩ hr
  exact fusionRecover (transition H M contextWindow) (suc z) count state next out c hone hsum

theorem rejectingFirstIterate (H : Program 1) (M contextWindow : Program 2) (count state c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph2 (transition H M contextWindow) z state c))) :
    Nonempty (Derivation body Gamma (graph3 (iterate H M contextWindow) z (suc count) state c)) :=
  iterateAfterFirst H M contextWindow count state z z c hf (iterateFailure H M contextWindow count c)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationProof
