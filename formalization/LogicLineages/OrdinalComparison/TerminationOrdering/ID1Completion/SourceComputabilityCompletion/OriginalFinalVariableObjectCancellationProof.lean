module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectFixednessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalFinalVariableCanonicalSupportProof (iffForward)
open OriginalFinalVariableObject OriginalFinalVariableObjectInternalSupportProof OriginalFinalVariableObjectFixednessProof
open OriginalRawObjectTransport

/-- The chain consists entirely of the literal Object programs. Shifted
canonical identity comes from the unchanged original source/window premises;
actual all-raw Object cancellation supplies erasure, then wrapper
functionality compares the two genuine final outputs. -/
theorem actualOriginalFinalVariableObjectCancellation :
    OriginalFinalVariableObjectTargets.ActualOriginalFinalVariableObjectCancellation := by
  intro guard p body alpha Delta shiftOut canonicalShift erased out originalOut input raw shifted variableCode
    shiftedVariable typ index parameter extendedParameter context gamma extendedGamma addedType
  let K := canonicalObjectProgram (OriginalVariableLeaves.refineInputs guard p)
  let A := Premise guard p input raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  let C := graph2 shiftObjectRaw shiftOut addedType input ⊓
    (graph2 K canonicalShift context shiftOut ⊓
      (graph1 eraseObjectRaw erased canonicalShift ⊓
        (graph2 K out context erased ⊓ graph2 K originalOut context input)))
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hfixed⟩ := actualOriginalFinalVariableObjectFixedness guard p body alpha (A :: Delta)
    originalOut canonicalShift input shiftOut raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  obtain ⟨ha'⟩ := ha
  have hf := andRight (show Nonempty (Derivation body (A :: Delta) _) from
    ⟨Derivation.implicationElimination hfixed ha'⟩)
  have hc : Nonempty (Derivation body (C :: A :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf'⟩ := addAssumption hf C
  obtain ⟨hs⟩ := andLeft hc
  have hshiftEquation := show Nonempty (Derivation body (C :: A :: Delta) _) from
    ⟨Derivation.implicationElimination hf' hs⟩
  have hcanonicalEq := iffForward hshiftEquation (andLeft (andRight hc))
  have herased := headTransport eraseObjectRaw erased canonicalShift shiftOut Fin.elim0
    (by simpa only [equalEqn] using hcanonicalEq) (andLeft (andRight (andRight hc)))
  have hinverse := OriginalRawObjectTransportInternalCancellationProof.objectRightInverse
    addedType input shiftOut (andLeft hc)
  have herasedEq := valueUnique eraseObjectRaw erased input (Fin.cons shiftOut Fin.elim0) herased hinverse
  have hout := secondTransport K out context erased input
    (by simpa only [equalEqn] using herasedEq) (andLeft (andRight (andRight (andRight hc))))
  obtain ⟨hresult⟩ := valueUnique K out originalOut (Fin.cons context (Fin.cons input Fin.elim0))
    hout (andRight (andRight (andRight (andRight hc))))
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction
    (by simpa only [equalEqn] using hresult))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectCancellationProof
