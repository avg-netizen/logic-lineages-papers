module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalFixednessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalResultFold (foldN foldGraph)
open OriginalFinalVariableCanonical OriginalFinalVariableCanonicalSupportProof
open OriginalFinalVariableCanonicalFixednessProof OriginalFinalVariableCanonicalRawProof
open OriginalRawSyntaxTransport
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Every stage is an actual graph of the original operation. Functionality
identifies the shift output, SAME-final rigidity identifies the intermediate
canonical output, and actual erasure cancellation identifies the restored raw.
The final equality then uses the SAME final fold at the SAME original input. -/
theorem actualChain (data : Data)
    (shiftOut canonicalShift erased out originalOut raw shifted parameter extendedParameter addedType : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (graph2 shiftPackedRaw shifted (numeral 0) raw)))
    (he : Nonempty (Derivation body Gamma (graph3 erasePackedRaw raw addedType (numeral 0) shifted)))
    (hf : Nonempty (Derivation body Gamma
      ((foldGraph data canonicalShift shifted extendedParameter).iff (equal canonicalShift shifted))))
    (hc : Nonempty (Derivation body Gamma
      (graph2 shiftPackedRaw shiftOut (numeral 0) raw ⊓
        (foldGraph data canonicalShift shiftOut extendedParameter ⊓
          (graph3 erasePackedRaw erased addedType (numeral 0) canonicalShift ⊓
            (foldGraph data out erased parameter ⊓ foldGraph data originalOut raw parameter)))))) :
    Nonempty (Derivation body Gamma (equal out originalOut)) := by
  have hshift := valueUnique shiftPackedRaw shiftOut shifted
    (Fin.cons (numeral 0) (Fin.cons raw Fin.elim0)) (andLeft hc) hs
  have hcanonical := headTransport (foldN data) canonicalShift shiftOut shifted
    (Fin.cons extendedParameter Fin.elim0) hshift (andLeft (andRight hc))
  have hcanonicalEq := iffForward hf hcanonical
  have herased := thirdTransport erasePackedRaw erased addedType (numeral 0) canonicalShift shifted
    hcanonicalEq (andLeft (andRight (andRight hc)))
  have herasedEq := valueUnique erasePackedRaw erased raw
    (Fin.cons addedType (Fin.cons (numeral 0) (Fin.cons shifted Fin.elim0))) herased he
  have hout := headTransport (foldN data) out erased raw (Fin.cons parameter Fin.elim0)
    herasedEq (andLeft (andRight (andRight (andRight hc))))
  simpa only [equalEqn] using valueUnique (foldN data) out originalOut
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) hout (andRight (andRight (andRight (andRight hc))))

/-- Literal shift/erasure and both canonicalizations coexist at the final
variable-refined tuple, with no native evaluation or assumed output identity. -/
theorem actualOriginalFinalVariableCancellation :
    OriginalFinalVariableCanonicalTargets.ActualOriginalFinalVariableCancellation := by
  intro guard p body alpha Delta shiftOut canonicalShift erased out originalOut raw shifted variableCode
    shiftedVariable typ index parameter extendedParameter context gamma extendedGamma addedType
  let data := OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p)
  let A := OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
      parameter extendedParameter context gamma extendedGamma addedType ⊓
    (graph2 (originalSourceValidity guard p) (numeral 1) raw parameter ⊓
      originalWindowGraph p raw parameter)
  let C := graph2 shiftPackedRaw shiftOut (numeral 0) raw ⊓
    (foldGraph data canonicalShift shiftOut extendedParameter ⊓
      (graph3 erasePackedRaw erased addedType (numeral 0) canonicalShift ⊓
        (foldGraph data out erased parameter ⊓ foldGraph data originalOut raw parameter)))
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andLeft ha
  have htransport := packedVariableTransport raw shifted variableCode shiftedVariable typ index addedType
    (andLeft hs) (andLeft (andRight hs)) (andLeft (andRight (andRight hs)))
    (andLeft (andRight (andRight (andRight hs))))
  obtain ⟨hfixed⟩ := actualOriginalFinalVariableFixedness guard p body alpha (A :: Delta)
    originalOut canonicalShift raw shifted variableCode shiftedVariable typ index parameter extendedParameter
    context gamma extendedGamma addedType
  obtain ⟨ha'⟩ := ha
  have hf := andRight (show Nonempty (Derivation body (A :: Delta) _) from
    ⟨Derivation.implicationElimination hfixed ha'⟩)
  obtain ⟨hc⟩ := actualChain data shiftOut canonicalShift erased out originalOut raw shifted
    parameter extendedParameter addedType (addAssumption htransport.1 C)
    (addAssumption htransport.2 C) (addAssumption hf C)
    (show Nonempty (Derivation body (C :: A :: Delta) C) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hr⟩ := andIntro htransport.1 (andIntro htransport.2
    (show Nonempty (Derivation body (A :: Delta) (C.imp (equal out originalOut))) from
      ⟨Derivation.implicationIntroduction hc⟩))
  exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalCancellationProof
