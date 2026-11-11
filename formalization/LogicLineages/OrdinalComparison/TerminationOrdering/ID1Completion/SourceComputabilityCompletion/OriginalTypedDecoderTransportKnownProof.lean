module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportRejectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportKnownProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableConstructorValue bottomConstructorValue)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderTransport
open OriginalTypedDecoderTransportLeafProof OriginalTypedDecoderTransportUnaryTagsProof
open OriginalTypedDecoderTransportBinaryTagsProof OriginalTypedDecoderTransportRejectedProof
open OriginalTypedDecoderTransportTagSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem termKnown (H : Program 1) (erasing : Bool) (i : Fin 8)
    (raw out d cutoff gamma extended typ payload : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H false typ raw (sourceContext erasing gamma extended))))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (Accepted H false typ out (targetContext erasing gamma extended))) := by
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact variableBranch H erasing raw out d cutoff gamma extended typ payload
      (variableConstructorValue raw payload hp) hi ho ha
  · intro ht hp
    exact lambdaTag H erasing raw out d cutoff gamma extended typ hind ht hi ho ha
  · intro ht hp
    exact applicationTag H erasing raw out d cutoff gamma extended typ hind ht hi ho ha
  · intro ht hp
    exact bottomBranch H erasing raw out d cutoff gamma extended typ payload
      (bottomConstructorValue raw payload hp) ho ha
  · intro ht hp
    exact ordinaryTag H erasing raw out d cutoff gamma extended typ hind ht hi ho ha
  · intro ht hp
    exact numberedTag H erasing raw out d cutoff gamma extended typ hind ht hi ho ha
  · intro ht hp
    exact termSix H raw payload typ (sourceContext erasing gamma extended) _ hp ha
  · intro ht hp
    exact termSeven H raw payload typ (sourceContext erasing gamma extended) _ hp ha

theorem argumentsKnown (H : Program 1) (erasing : Bool) (i : Fin 8)
    (raw out d cutoff gamma extended typ payload : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H erasing raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H true typ raw (sourceContext erasing gamma extended))))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (Accepted H true typ out (targetContext erasing gamma extended))) := by
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact argumentsOther H 0 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) _ hp ha
  · intro ht hp
    exact argumentsOther H 1 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) _ hp ha
  · intro ht hp
    exact argumentsOther H 2 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) _ hp ha
  · intro ht hp
    exact argumentsOther H 3 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) _ hp ha
  · intro ht hp
    exact argumentsOther H 4 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) _ hp ha
  · intro ht hp
    exact argumentsOther H 5 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) _ hp ha
  · intro ht hp
    exact nilBranch H erasing raw out d cutoff gamma extended typ
      (acceptedNilConstructor H raw payload typ (sourceContext erasing gamma extended) hp ha) ho ha
  · intro ht hp
    exact consTag H erasing raw out d cutoff gamma extended typ hind ht hi ho ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportKnownProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportKnownProof
