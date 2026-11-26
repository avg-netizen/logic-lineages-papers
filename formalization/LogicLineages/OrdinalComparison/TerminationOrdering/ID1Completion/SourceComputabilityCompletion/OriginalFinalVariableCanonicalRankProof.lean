module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalFixednessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalFinalVariableCanonical OriginalFinalVariableCanonicalSupportProof
open OriginalFinalVariableCanonicalFixednessProof OriginalFinalVariableCanonicalRawProof
open OriginalRawSyntaxTransport

/-- All symbolic rank outputs are preserved at both actual final-fold
endpoints. Their identities are derived from the original source/window rule,
not supplied as premises or borrowed from native Object calibration. -/
theorem actualOriginalFinalVariableRankPreservation :
    OriginalFinalVariableCanonicalTargets.ActualOriginalFinalVariableRankPreservation := by
  intro guard p body alpha Delta rank out shiftedOut raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  let data := OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p)
  let A := OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
      parameter extendedParameter context gamma extendedGamma addedType ⊓
    (graph2 (originalSourceValidity guard p) (numeral 1) raw parameter ⊓
      originalWindowGraph p raw parameter)
  let C := foldGraph data out raw parameter ⊓ foldGraph data shiftedOut shifted extendedParameter
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andLeft ha
  have hr := packedVariableRankEquation rank raw variableCode typ index
    (andLeft hs) (andLeft (andRight (andRight hs)))
  have hsr := packedVariableRankEquation rank shifted shiftedVariable typ (OrdinaryArithmetic.succTerm index)
    (andLeft (andRight hs)) (andLeft (andRight (andRight (andRight hs))))
  obtain ⟨hfixed⟩ := actualOriginalFinalVariableFixedness guard p body alpha (A :: Delta)
    out shiftedOut raw shifted variableCode shiftedVariable typ index parameter extendedParameter
    context gamma extendedGamma addedType
  obtain ⟨ha'⟩ := ha
  have hf := show Nonempty (Derivation body (A :: Delta) _) from
    ⟨Derivation.implicationElimination hfixed ha'⟩
  have hc : Nonempty (Derivation body (C :: A :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hco⟩ := andIntro
    (rankInputEquation rank out raw (iffForward (addAssumption (andLeft hf) C) (andLeft hc)))
    (rankInputEquation rank shiftedOut shifted (iffForward (addAssumption (andRight hf) C) (andRight hc)))
  obtain ⟨result⟩ := andIntro hr (andIntro hsr
    (show Nonempty (Derivation body (A :: Delta) _) from ⟨Derivation.implicationIntroduction hco⟩))
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRankProof
