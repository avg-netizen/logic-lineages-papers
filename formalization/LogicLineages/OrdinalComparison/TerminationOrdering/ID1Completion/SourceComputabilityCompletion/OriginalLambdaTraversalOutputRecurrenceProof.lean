module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLeafCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafOtherTagProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputRecurrenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalOutput
open OriginalLambdaTraversalInternalTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Modular induction step. The one generic machine recurrence supplier is
explicit here and must be discharged by its independent internal proof in
the final OutputLaws theorem; no source-specific hypothesis replaces it. -/
theorem applicationAtOutputs (recurrence : ActualOriginalLambdaTraversalInternalApplication)
    (rawData : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out typ parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg parent)))
    (hs : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) parent typ parameter)))
    (hr : Nonempty (Derivation body Delta (graph4 application out d e functionOut argumentOut)))
    (hfi : Nonempty (Derivation body Delta (outputInvariant rawData window functionOut fn arrow parameter)))
    (hai : Nonempty (Derivation body Delta (outputInvariant rawData window argumentOut arg d parameter))) :
    Nonempty (Derivation body Delta (outputInvariant rawData window out parent typ parameter)) := by
  have hi := OriginalLambdaTraversalOutputApplicationCoreProof.applicationAtOutputs
    rawData window arrow d e fp ap fn arg parent functionOut argumentOut out typ parameter hc hs hr hfi hai
  have fields := OriginalLambdaTraversalApplicationFieldsProof.fromRaw arrow d e functionOut argumentOut out
    (andLeft hc) (andLeft (andRight hfi)) (andLeft (andRight hai)) hr
  obtain ⟨law⟩ := recurrence body (leaf rawData window) alpha Delta
    out d e functionOut argumentOut functionOut argumentOut out parameter
  obtain ⟨hp⟩ := andIntro fields (andIntro (andRight (andRight (andRight hfi)))
    (andRight (andRight (andRight hai))))
  obtain ⟨hr⟩ := hr
  have hf := Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination law hp)) hr
  exact andIntro (andLeft hi) (andIntro (andLeft (andRight hi))
    (andIntro (andRight (andRight hi)) ⟨hf⟩))

/-- The base case uses selected-leaf idempotence and literal preservation of
OTHER tags. The original C graph is not replaced by a native equality. -/
theorem otherAtOutput (recurrence : ActualOriginalLambdaTraversalInternalLeaf)
    (rawData : Data) (window : Program 1) (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises rawData window out input typ parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input))) :
    Nonempty (Derivation body Delta (outputInvariant rawData window out input typ parameter)) := by
  obtain ⟨law⟩ := recurrence body (leaf rawData window) alpha Delta input out parameter
  obtain ⟨htProof⟩ := ht
  obtain ⟨hc⟩ := andRight (andRight hp)
  have hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination law htProof)) hc⟩
  have hi := OriginalLambdaTraversalOutputLeafCoreProof.leafOutput
    rawData window out input typ parameter hl (andLeft (andRight hp))
  have hother := OriginalLambdaTraversalLeafOtherTagProof.leafOtherTag
    rawData window out input parameter (andLeft hp) (andLeft (andLeft (andRight hp))) hl ⟨htProof⟩
  obtain ⟨fixedLaw⟩ := recurrence body (leaf rawData window) alpha Delta out out parameter
  obtain ⟨hother⟩ := hother
  obtain ⟨hfixedLeaf⟩ := andRight (andRight (andRight hi))
  have hfixed := Derivation.implicationElimination (Derivation.conjunctionRight
    (Derivation.implicationElimination fixedLaw hother)) hfixedLeaf
  exact andIntro (andLeft hi) (andIntro (andLeft (andRight hi))
    (andIntro (andLeft (andRight (andRight hi))) ⟨hfixed⟩))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputRecurrenceProof
