module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalTransparentDecoderFinalTransportObject
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The wrapper's two inputs are recovered at literal original Object and
parameter pairs. The underlying validator remains an arbitrary unchanged AST. -/
theorem objectComponents (c input gamma packed parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input gamma packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma))) :
    Nonempty (Derivation body Delta
      (graph2 (rightOf (.projection 1)) packed c input)) ∧
    Nonempty (Derivation body Delta
      (graph2 (pairOf (.projection 0) (leftOf (.projection 1))) parameter c input)) := by
  let xs : Fin 2 → OTerm alpha := ![c,input]
  have hl := unaryValue InternalUnpair.left (.projection 1) gamma input xs
    (pairLeft input gamma packed hp) (projectionValue 1 xs)
  have hr := unaryValue InternalUnpair.right (.projection 1) packed input xs
    (pairRight input gamma packed hp) (projectionValue 1 xs)
  exact ⟨hr,binaryValue InternalPairing.pairing (.projection 0) (leftOf (.projection 1))
    parameter c gamma xs hc (projectionValue 0 xs) hl⟩

theorem objectFieldsIntro (validator : Program 2)
    (out c input gamma packed parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input gamma packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (ha : Nonempty (Derivation body Delta (graph2 validator out packed parameter))) :
    Nonempty (Derivation body Delta (graph2 (objectValidator validator) out c input)) := by
  have hv := objectComponents c input gamma packed parameter hp hc
  exact binaryValue validator (rightOf (.projection 1))
    (pairOf (.projection 0) (leftOf (.projection 1))) out packed parameter ![c,input] ha hv.1 hv.2

theorem objectFieldsElim (validator : Program 2)
    (out c input gamma packed parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing input gamma packed)))
    (hc : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (ha : Nonempty (Derivation body Delta (graph2 (objectValidator validator) out c input))) :
    Nonempty (Derivation body Delta (graph2 validator out packed parameter)) := by
  have hv := objectComponents c input gamma packed parameter hp hc
  exact binaryRecover validator (rightOf (.projection 1))
    (pairOf (.projection 0) (leftOf (.projection 1))) out packed parameter ![c,input] ha hv.1 hv.2

theorem implicationApply {A B : Formula alpha}
    (h : Nonempty (Derivation body Delta (A.imp B)))
    (ha : Nonempty (Derivation body Delta A)) :
    Nonempty (Derivation body Delta B) := by
  obtain ⟨h⟩ := h
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination h ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportObjectFieldsProof
