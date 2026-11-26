module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder (ifSame)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalRequestSelectorsProof OriginalTypedDecoderInternalBranchProof
open OriginalUniverseDecoderInternalBooleanProof OriginalUniverseDecoder
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem requestModeType (r m g t rawCode c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r m g t rawCode))) :
    Nonempty (Derivation body Delta (graph2 mode m r c)) ∧
      Nonempty (Derivation body Delta (graph2 typ t r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hf := fun i => requestFieldValue request i r m g t rawCode xs (projectionValue 0 xs) hr
  exact ⟨hf 0,hf 2⟩

theorem requestTagPayload (r m g t rawCode v p c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r m g t rawCode)))
    (hp : Nonempty (Derivation body Delta (StepPair rawCode v p))) :
    Nonempty (Derivation body Delta (graph2 tag v r c)) ∧
      Nonempty (Derivation body Delta (graph2 payload p r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hraw := requestFieldValue request 3 r m g t rawCode xs (projectionValue 0 xs) hr
  exact ⟨pairLeftValue raw rawCode v p xs hraw hp,
    pairRightValue raw rawCode v p xs hraw hp⟩

theorem termRootForward (M W : Program 2) (r g t rawCode c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 0) g t rawCode)))
    (ho : Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta
      (graph2 M (numeral 1) t c ⊓ graph2 (extraGuard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hf := requestModeType r (numeral 0) g t rawCode c hr
  have he : Nonempty (Derivation body Delta (equal (numeral 0 : OTerm alpha) (numeral 0))) := by
    rw [equalEqn]; exact ⟨refl (numeral 0)⟩
  have hroot := sameYesElim mode (constant 2 0)
    (ifSame (memberAt M typ) (constant 2 1) (extraGuard M W) (constant 2 0))
    (ifSame mode (constant 2 1) (constant 2 1) (constant 2 0))
    (numeral 1) (numeral 0) (numeral 0) xs hf.1 (constantValue 0 xs) he ho
  have hparts := filterForward (memberAt M typ) (extraGuard M W) xs hroot
  exact andIntro
    (binaryRecover M typ context (numeral 1) t c xs (andLeft hparts) hf.2 (projectionValue 1 xs))
    (andRight hparts)

theorem termRootBackward (M W : Program 2) (r g t rawCode c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 0) g t rawCode)))
    (hm : Nonempty (Derivation body Delta (graph2 M (numeral 1) t c)))
    (he : Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hf := requestModeType r (numeral 0) g t rawCode c hr
  have hz : Nonempty (Derivation body Delta (equal (numeral 0 : OTerm alpha) (numeral 0))) := by
    rw [equalEqn]; exact ⟨refl (numeral 0)⟩
  apply sameYesIntro mode (constant 2 0)
    (ifSame (memberAt M typ) (constant 2 1) (extraGuard M W) (constant 2 0))
    (ifSame mode (constant 2 1) (constant 2 1) (constant 2 0))
    (numeral 1) (numeral 0) (numeral 0) xs hf.1 (constantValue 0 xs) hz
  exact filterBackward (memberAt M typ) (extraGuard M W) xs
    (binaryValue M typ context (numeral 1) t c xs hm hf.2 (projectionValue 1 xs)) he

theorem argumentsGuard (M W : Program 2) (r g t rawCode c : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r (numeral 1) g t rawCode))) :
    Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hf := requestModeType r (numeral 1) g t rawCode c hr
  have he : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  apply sameNoIntro mode (constant 2 0) _ _ (numeral 1) (numeral 1) (numeral 0) xs
    hf.1 (constantValue 0 xs) (excludeNumeral (numeral 1) 1 0 (by decide) he)
  exact sameYesIntro mode (constant 2 1) (constant 2 1) (constant 2 0)
    (numeral 1) (numeral 1) (numeral 1) xs hf.1 (constantValue 1 xs) he (constantValue 1 xs)

/-- Variable, application, bottom and rejected tags carry no constructor-
specific guard in addition to their original root type membership. -/
theorem neutralExtra (M W : Program 2) (i : Nat) (h1 : i ≠ 1) (h4 : i ≠ 4) (h5 : i ≠ 5)
    (r c : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 tag (numeral i) r c))) :
    Nonempty (Derivation body Delta (graph2 (extraGuard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have he : Nonempty (Derivation body Delta (equal (numeral i : OTerm alpha) (numeral i))) := by
    rw [equalEqn]; exact ⟨refl (numeral i)⟩
  apply sameNoIntro tag (constant 2 1) _ _ (numeral 1) (numeral i) (numeral 1) xs
    hv (constantValue 1 xs) (excludeNumeral (numeral i) i 1 h1 he)
  apply sameNoIntro tag (constant 2 4) _ _ (numeral 1) (numeral i) (numeral 4) xs
    hv (constantValue 4 xs) (excludeNumeral (numeral i) i 4 h4 he)
  exact sameNoIntro tag (constant 2 5) _ _ (numeral 1) (numeral i) (numeral 5) xs
    hv (constantValue 5 xs) (excludeNumeral (numeral i) i 5 h5 he) (constantValue 1 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceGuardRootProof
