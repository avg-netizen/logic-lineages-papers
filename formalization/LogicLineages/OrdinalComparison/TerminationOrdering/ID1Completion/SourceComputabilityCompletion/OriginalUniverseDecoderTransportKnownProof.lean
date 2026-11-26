module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportRejectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTagSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableConstructorValue bottomConstructorValue)
open OriginalTypedDecoderStepSpecification
open OriginalUniverseDecoderTransport
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalUniverseDecoderTransportLeafProof OriginalUniverseDecoderTransportUnaryTagsProof
open OriginalUniverseDecoderTransportBinaryTagsProof OriginalUniverseDecoderTransportRejectedProof
open OriginalUniverseDecoderTransportTagSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem termKnown (H : Program 1) (M W : Program 2) (erasing : Bool) (i : Fin 8)
    (raw out d cutoff gamma extended typ payload c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ raw (sourceContext erasing gamma extended) c)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ out (targetContext erasing gamma extended) c)) := by
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact variableBranch H M W erasing raw out d cutoff gamma extended typ payload c
      (variableConstructorValue raw payload hp) hi ho ha
  · intro ht hp
    exact lambdaTag H M W erasing raw out d cutoff gamma extended typ c hind ht hi ho ha
  · intro ht hp
    exact applicationTag H M W erasing raw out d cutoff gamma extended typ c hind ht hi ho ha
  · intro ht hp
    exact bottomBranch H M W erasing raw out d cutoff gamma extended typ payload c
      (bottomConstructorValue raw payload hp) ho ha
  · intro ht hp
    exact ordinaryTag H M W erasing raw out d cutoff gamma extended typ c hind ht hi ho ha
  · intro ht hp
    exact numberedTag H M W erasing raw out d cutoff gamma extended typ c hind ht hi ho ha
  · intro ht hp
    exact termSix H M W raw payload typ (sourceContext erasing gamma extended) c _ hp ha
  · intro ht hp
    exact termSeven H M W raw payload typ (sourceContext erasing gamma extended) c _ hp ha

theorem argumentsKnown (H : Program 1) (M W : Program 2) (erasing : Bool) (i : Fin 8)
    (raw out d cutoff gamma extended typ payload c : OTerm alpha)
    (hind : Nonempty (Derivation body Delta (BelowRaw H M W erasing raw)))
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (ho : Nonempty (Derivation body Delta (graph3 (fold (selectedMode erasing)) out d cutoff raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true typ raw (sourceContext erasing gamma extended) c)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral i.val) raw)))
    (hp : Nonempty (Derivation body Delta (StepPair raw (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (Accepted H M W true typ out (targetContext erasing gamma extended) c)) := by
  revert ht hp
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)))))))) i
  · intro ht hp
    exact argumentsOther H M W 0 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 1 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 2 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 3 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 4 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) c _ hp ha
  · intro ht hp
    exact argumentsOther H M W 5 (by decide) (by decide) raw payload typ (sourceContext erasing gamma extended) c _ hp ha
  · intro ht hp
    exact nilBranch H M W erasing raw out d cutoff gamma extended typ c
      (acceptedNilConstructor H M W raw payload typ (sourceContext erasing gamma extended) c hp ha) ho ha
  · intro ht hp
    exact consTag H M W erasing raw out d cutoff gamma extended typ c hind ht hi ho ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportKnownProof
