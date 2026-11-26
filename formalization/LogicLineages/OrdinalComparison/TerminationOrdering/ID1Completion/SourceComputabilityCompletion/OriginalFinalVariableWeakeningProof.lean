module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalVariableLeaves OriginalFinalVariableWeakening
open OriginalFinalVariableWeakeningTransportProof OriginalTransparentLambdaFinalLogicProof
open OriginalFinalOtherValidityProof
open UniformCertificateCompletion

/-- Original all-output source validity is preserved at the very SAME final
Data. The original source AND target leaves are both transported internally. -/
theorem actualOriginalFinalVariableSourceWeakening :
    OriginalFinalVariableWeakeningTargets.ActualOriginalFinalVariableSourceWeakening := by
  intro guard p body alpha Delta out raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  let S := Shape raw shifted variableCode shiftedVariable typ index parameter extendedParameter
    context gamma extendedGamma addedType
  have hs : Nonempty (Derivation body (S :: Delta) S) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ho := otherBoth raw shifted variableCode shiftedVariable typ index parameter extendedParameter
    context gamma extendedGamma addedType hs
  have hl := leafTransport guard p.base (numeral 1) raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType hs
  obtain ⟨hf⟩ := actualOriginalFinalOtherSourceValidity (refineInputs guard p)
    body alpha (S :: Delta) out raw parameter
  obtain ⟨hb⟩ := actualOriginalFinalOtherSourceValidity (refineInputs guard p)
    body alpha (S :: Delta) out shifted extendedParameter
  obtain ⟨ho1⟩ := ho.1
  obtain ⟨ho2⟩ := ho.2
  obtain ⟨h⟩ := iffCompose ⟨Derivation.implicationElimination hf ho1⟩
    (iffCompose (booleanIff out (andIff hl.1 hl.2))
      (iffReverse ⟨Derivation.implicationElimination hb ho2⟩))
  exact ⟨Derivation.implicationIntroduction h⟩

/-- The same final target retains the unchanged outer Context guard and
transports only the actual cons-successor dependent-decoder coordinates. -/
theorem actualOriginalFinalVariableTargetWeakening :
    OriginalFinalVariableWeakeningTargets.ActualOriginalFinalVariableTargetWeakening := by
  intro guard p body alpha Delta out raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  let S := Shape raw shifted variableCode shiftedVariable typ index parameter extendedParameter
    context gamma extendedGamma addedType
  have hs : Nonempty (Derivation body (S :: Delta) S) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ho := otherBoth raw shifted variableCode shiftedVariable typ index parameter extendedParameter
    context gamma extendedGamma addedType hs
  have hl := leafTransport guard p.base (numeral 1) raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType hs
  obtain ⟨hf⟩ := actualOriginalFinalOtherTargetValidity (refineInputs guard p)
    body alpha (S :: Delta) out raw parameter
  obtain ⟨hb⟩ := actualOriginalFinalOtherTargetValidity (refineInputs guard p)
    body alpha (S :: Delta) out shifted extendedParameter
  obtain ⟨ho1⟩ := ho.1
  obtain ⟨ho2⟩ := ho.2
  obtain ⟨h⟩ := iffCompose ⟨Derivation.implicationElimination hf ho1⟩
    (iffCompose (booleanIff out hl.2)
      (iffReverse ⟨Derivation.implicationElimination hb ho2⟩))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningProof
