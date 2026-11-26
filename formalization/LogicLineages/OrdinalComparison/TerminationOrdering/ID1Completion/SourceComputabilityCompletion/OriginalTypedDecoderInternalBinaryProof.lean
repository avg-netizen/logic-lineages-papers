module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalBinarySyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryDomainValue {n : Nat} (p : Program n) (code d first second : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hf : Nonempty (Derivation body Delta (StepBinaryPayload code d first second))) :
    Nonempty (Derivation body Delta (programGraph (leftOf p) d xs)) := by
  apply stepBinaryPayloadCases code d first second _ hf
  intro beta j Theta tail hj hpair _
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  rw [programRename] at hp'
  exact pairLeftValue p (code.relabel j) (d.relabel j) tail
    (fun i => (xs i).relabel j) hp' hpair

theorem binaryFirstValue {n : Nat} (p : Program n) (code d first second : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hf : Nonempty (Derivation body Delta (StepBinaryPayload code d first second))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf p)) first xs)) := by
  apply stepBinaryPayloadCases code d first second _ hf
  intro beta j Theta tail hj hpair htail
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  rw [programRename] at hp'
  let xx := fun i => (xs i).relabel j
  have ht := pairRightValue p (code.relabel j) (d.relabel j) tail xx hp' hpair
  exact pairLeftValue (rightOf p) tail (first.relabel j) (second.relabel j) xx ht htail

theorem binarySecondValue {n : Nat} (p : Program n) (code d first second : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hf : Nonempty (Derivation body Delta (StepBinaryPayload code d first second))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf p)) second xs)) := by
  apply stepBinaryPayloadCases code d first second _ hf
  intro beta j Theta tail hj hpair htail
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  rw [programRename] at hp'
  let xx := fun i => (xs i).relabel j
  have ht := pairRightValue p (code.relabel j) (d.relabel j) tail xx hp' hpair
  exact pairRightValue (rightOf p) tail (first.relabel j) (second.relabel j) xx ht htail

theorem binaryFields {n : Nat} (p : Program n) (code d first second : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hd : Nonempty (Derivation body Delta (programGraph (leftOf p) d xs)))
    (hf : Nonempty (Derivation body Delta (programGraph (leftOf (rightOf p)) first xs)))
    (hs : Nonempty (Derivation body Delta (programGraph (rightOf (rightOf p)) second xs))) :
    Nonempty (Derivation body Delta (StepBinaryPayload code d first second)) := by
  apply programCases (rightOf p) xs _
  intro beta j Theta tail hj htail
  rw [stepBinaryPayloadRename]
  have hp' := renameInto hp j Theta hj
  have hd' := renameInto hd j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [programRename] at hp' hd' hf' hs'
  let xx := fun i => (xs i).relabel j
  exact stepBinaryPayloadIntro _ _ _ _ tail
    (pairFields p (code.relabel j) (d.relabel j) tail xx hp' hd' htail)
    (pairFields (rightOf p) tail (first.relabel j) (second.relabel j) xx htail hf' hs')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinaryProof
