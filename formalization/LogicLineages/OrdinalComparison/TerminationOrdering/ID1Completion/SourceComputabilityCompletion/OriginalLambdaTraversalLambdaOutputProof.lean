module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRebuildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalLambdaTraversalLambdaRootProof OriginalLambdaTraversalLambdaSourceProof
open OriginalLambdaTraversalLambdaRebuildProof OriginalLambdaTraversalLambdaOrderProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The parent premises internally supply both the actual child source/type
and the SAME window at the actual extended parameter required by induction. -/
theorem childPremises (rawData : Data) (window : Program 1)
    (raw d e child typ parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (LambdaFields raw d e child parameter bodyParameter)))
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window raw parameter)))
    (hs : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) raw typ parameter))) :
    Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph window child bodyParameter ⊓
        InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) child e bodyParameter)) :=
  andIntro
    (OriginalLambdaTraversalLambdaWindowProof.windowChild window InternalOriginalStepGuard.one
      raw child parameter bodyParameter (andRight (andRight (andRight (andRight hf)))) hw)
    (sourceChild rawData window raw d e child parameter bodyParameter hf (andLeft hs))

/-- The constructor-algebra portion of the exact frozen output invariant:
SAME source, SAME parent type and raw-code nonincrease, plus literal rebuilt
fields at the unchanged child parameter. C-idempotence remains a separate
recurrence consumer and is not asserted by this helper. -/
theorem outputRebuild (rawData : Data) (window : Program 1)
    (raw out d e child childOut typ parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (LambdaFields raw d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (leafData rawData window) raw typ parameter)))
    (hb : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) childOut bodyParameter ⊓
        (graph1 InternalUnpair.left e childOut ⊓ InternalParameterizedBoundedDescentNormalizer.atMost childOut child))))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) out parameter ⊓
        (graph1 InternalUnpair.left typ out ⊓
          (InternalParameterizedBoundedDescentNormalizer.atMost out raw ⊓
            LambdaFields out d e childOut parameter bodyParameter)))) := by
  have hsource := andLeft hs
  have htype := andRight hs
  have rebuilt := sourceRebuild rawData window raw out d e child childOut typ parameter bodyParameter
    hf htype hsource (andLeft hb) (andLeft (andRight hb)) hc
  have oldConstructor := andRight (sourceConstructor rawData window raw d e child typ parameter bodyParameter
    hf htype hsource)
  have oldType := andRight (sourceChild rawData window raw d e child parameter bodyParameter hf hsource)
  have bound := lambdaBound d e child childOut raw out oldType (andLeft (andRight hb))
    oldConstructor hc (andRight (andRight hb))
  exact andIntro (andLeft rebuilt)
    (andIntro (andRight (andRight rebuilt)) (andIntro bound (andLeft (andRight rebuilt))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
