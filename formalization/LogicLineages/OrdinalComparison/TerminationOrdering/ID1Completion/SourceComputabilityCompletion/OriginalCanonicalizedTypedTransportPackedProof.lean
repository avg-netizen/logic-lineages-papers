module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportMembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportOuterTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportPackedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (selectedTyped validity)
open InternalOriginalUniformDescentSelectionInternalProof (typedRecover)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open OriginalCanonicalizedTypedTransportMembershipProof
open OriginalCanonicalizedTypedTransportOuterTypeProof
open OriginalCanonicalizedTypedTransportFoldProof
open OriginalTransparentDecoderFinalTransportProof
open OriginalTransparentDecoderValidatorCollapse
open OriginalContextInsertion OriginalRawSyntaxTransport
open UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Shift at an arbitrary insertion cutoff and canonicalize with the SAME
actual fold. Raw transformed fixedness is never used or asserted. -/
theorem weakeningAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (d cutoff gamma extended c parameter extendedParameter input shifted out typ : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hq : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing extendedParameter c extended)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted cutoff input)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (selectedTyped (selected p H G W)) (numeral 1) input typ parameter)))
    (hn : Nonempty (Derivation body Delta
      (foldGraph (selected p H G W) out shifted extendedParameter))) :
    Nonempty (Derivation body Delta
      (graph3 (selectedTyped (selected p H G W)) (numeral 1) out typ extendedParameter)) := by
  let data := selected p H G W
  have hf := typedRecover data.oldRepresentative (validity data) data.member
    input typ parameter ht
  have hv := impApply
    (actualOriginalTransparentDecoderFinalSourceWeakening p H G W body alpha Delta
      d cutoff gamma extended c parameter extendedParameter input shifted)
    (andIntro hi (andIntro hp (andIntro hq (andIntro hs (andLeft (andRight hf))))))
  have hl := shiftedLeft input shifted typ cutoff hs (andLeft (andRight (andRight hf)))
  have hm := memberTransport p H G W typ parameter extendedParameter c gamma extended
    hp hq (andLeft hf)
  exact foldTyped data out shifted typ extendedParameter hv hl hm hn

/-- Erase at the same insertion and canonicalize the actual erased output.
The original typed input pays membership; the fold pays output fixedness. -/
theorem erasureAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (d cutoff gamma extended c parameter extendedParameter input erased out typ : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (hq : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing extendedParameter c extended)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erased d cutoff input)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (selectedTyped (selected p H G W)) (numeral 1) input typ extendedParameter)))
    (hn : Nonempty (Derivation body Delta
      (foldGraph (selected p H G W) out erased parameter))) :
    Nonempty (Derivation body Delta
      (graph3 (selectedTyped (selected p H G W)) (numeral 1) out typ parameter)) := by
  let data := selected p H G W
  have hf := typedRecover data.oldRepresentative (validity data) data.member
    input typ extendedParameter ht
  have hv := impApply
    (actualOriginalTransparentDecoderFinalSourceErasure p H G W body alpha Delta
      d cutoff gamma extended c parameter extendedParameter input erased)
    (andIntro hi (andIntro hp (andIntro hq (andIntro he (andLeft (andRight hf))))))
  have hl := erasedLeft input erased typ d cutoff he (andLeft (andRight (andRight hf)))
  have hm := memberTransport p H G W typ extendedParameter parameter c extended gamma
    hq hp (andLeft hf)
  exact foldTyped data out erased typ parameter hv hl hm hn

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportPackedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportPackedProof
