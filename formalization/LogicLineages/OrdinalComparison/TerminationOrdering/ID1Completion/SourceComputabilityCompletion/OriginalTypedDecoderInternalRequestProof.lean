module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Unfold only the actual request constructor's pair compositions; its
intermediate codes are obtained internally from original Program totality. -/
theorem requestForward {n : Nat} (m g t r : Program n)
    (out mode gamma typ raw : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hm : Nonempty (Derivation body Delta (programGraph m mode xs)))
    (hg : Nonempty (Derivation body Delta (programGraph g gamma xs)))
    (ht : Nonempty (Derivation body Delta (programGraph t typ xs)))
    (hr : Nonempty (Derivation body Delta (programGraph r raw xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (pairOf m (pairOf g (pairOf t r))) out xs))) :
    Nonempty (Derivation body Delta (StepRequest out mode gamma typ raw)) := by
  apply queryCases (![pairOf g (pairOf t r),pairOf t r] : Fin 2 → Program n) xs _
  intro beta j ys Theta hj hq
  rw [stepRequestRename]
  have hm' := renameInto hm j Theta hj
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [programRename] at hm' hg' ht' hr' ho'
  let xx := fun i => (xs i).relabel j
  have houter := binaryRecover InternalPairing.pairing m (pairOf g (pairOf t r))
    (out.relabel j) (mode.relabel j) (ys 0) xx ho' hm' (hq 0)
  have hgamma := binaryRecover InternalPairing.pairing g (pairOf t r)
    (ys 0) (gamma.relabel j) (ys 1) xx (hq 0) hg' (hq 1)
  have htype := binaryRecover InternalPairing.pairing t r
    (ys 1) (typ.relabel j) (raw.relabel j) xx (hq 1) ht' hr'
  exact stepRequestIntro _ _ _ _ _ ys (andIntro houter (andIntro hgamma htype))

/-- The independently specified three original pairs rebuild the identical
request AST. No external decoded request or coding-validity premise is used. -/
theorem requestBackward {n : Nat} (m g t r : Program n)
    (out mode gamma typ raw : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hm : Nonempty (Derivation body Delta (programGraph m mode xs)))
    (hg : Nonempty (Derivation body Delta (programGraph g gamma xs)))
    (ht : Nonempty (Derivation body Delta (programGraph t typ xs)))
    (hr : Nonempty (Derivation body Delta (programGraph r raw xs)))
    (ho : Nonempty (Derivation body Delta (StepRequest out mode gamma typ raw))) :
    Nonempty (Derivation body Delta
      (programGraph (pairOf m (pairOf g (pairOf t r))) out xs)) := by
  apply stepRequestCases out mode gamma typ raw _ ho
  intro beta j Theta ys hj hq
  rw [programRename]
  have hm' := renameInto hm j Theta hj
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [programRename] at hm' hg' ht' hr'
  let xx := fun i => (xs i).relabel j
  have htype := binaryValue InternalPairing.pairing t r
    (ys 1) (typ.relabel j) (raw.relabel j) xx (andRight (andRight hq)) ht' hr'
  have hgamma := binaryValue InternalPairing.pairing g (pairOf t r)
    (ys 0) (gamma.relabel j) (ys 1) xx (andLeft (andRight hq)) hg' htype
  exact binaryValue InternalPairing.pairing m (pairOf g (pairOf t r))
    (out.relabel j) (mode.relabel j) (ys 0) xx (andLeft hq) hm' hgamma

theorem liveForward {n : Nat} (p : Program n) (out work : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p work xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (liveOf p) out xs))) :
    Nonempty (Derivation body Delta (StepLive out work)) :=
  binaryRecover InternalPairing.pairing (constant n 1) p out (numeral 1) work xs ho
    (constantValue 1 xs) hp

theorem liveBackward {n : Nat} (p : Program n) (out work : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p work xs)))
    (ho : Nonempty (Derivation body Delta (StepLive out work))) :
    Nonempty (Derivation body Delta (programGraph (liveOf p) out xs)) :=
  binaryValue InternalPairing.pairing (constant n 1) p out (numeral 1) work xs ho
    (constantValue 1 xs) hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
