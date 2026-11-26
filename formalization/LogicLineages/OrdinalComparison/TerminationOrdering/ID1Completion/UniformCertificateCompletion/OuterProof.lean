module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCertificateLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDomainForwardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationStepPeelSupportProof
open InternalComputabilityDownwardProof
open SourceComputabilityFormulaSupportProof
open SourceComputabilityCompletion

/-- The frozen concrete package: one source/computability/lift selection,
the original unqualified certificate lift, and full-type downward closure.
Original all-input calibrated existential selection is a separate target. -/
theorem actualConcreteUniformCertificateDownwardPackage :
    OuterTargets.ActualConcreteUniformCertificateDownwardPackage := by
  intro n arity base hc window hw oldSrc oldComp oldStep oldVertex oldResult
  dsimp only
  intro symbols S table hS
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := OuterSelection.data base window
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  let lift := OuterSelection.lift base window oldVertex
  have hwindow := OuterWindowProof.closedWindowEvaluation n window hw symbols S table hS
  have rules := OuterArithmeticProof.arithmeticRules oldSrc oldComp data (RawScalar.checker data)
    oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure window oldVertex oldResult context hwindow
  have certified := OuterCertificateLiftProof.certifiedApplicationLift n arity base hc window hw
    oldSrc oldComp oldStep oldVertex oldResult symbols S table hS
  refine ⟨rules, certified, ?_, ?_, ?_, ?_⟩
  · intro α tau x
    exact OuterCarrierProof.typedCarrierRule oldSrc oldComp data oldStep BottomRepresentative.bottomTest
      BottomSpineMeasure.measure window oldVertex oldResult context hwindow α tau x
  · exact OuterCarrierProof.domainCarrier oldSrc oldComp data oldStep BottomRepresentative.bottomTest
      BottomSpineMeasure.measure window oldVertex oldResult context hwindow
  · exact OuterDomainForwardProof.domainForward oldSrc oldComp data (RawScalar.checker data) oldStep
      BottomRepresentative.bottomTest BottomSpineMeasure.measure window oldVertex oldResult context hwindow
  · intro tau α f g
    let P := computable comp tau (numeral context) f ⊓ edge src false context f g
    have hp : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P] P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := actualOriginalComputabilityDownward src comp context rules
      (actualOriginalCertifiedLiftReduction src comp lift context certified)
      tau α [P] f g (andLeft hp) (andRight hp)
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterProof
