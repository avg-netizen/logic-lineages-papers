module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedTypedFocus
open NumberedNumericDecoding NumberedNumericCarrier NumberedStepCertificate
open NumberedNumericStep NumberedNumericStepPrimrec ApplicationCertificateLift
open NumberedMultisetNumeric NumberedFocusCode NumberedUniformPackedDecoding

theorem actualPathDecoderLift : ApplicationStepGuardTargets.ActualPathDecoderLift := by
  intro path
  obtain ⟨values, hv⟩ := NumberedMultisetNumericTotalityProof.decoderTotality path
  have he := NumberedMultisetNumericSupportProof.numbersSound path values hv
  have hp : decodeNumbers (1 + Nat.pair 2 path) = some (2 :: values) := by
    rw [← he]
    exact NumberedMultisetNumericSupportProof.numbersRoundTrip (2 :: values)
  have hposition : decodePosition 2 = some .appFunction := by
    change decodePosition (positionNumber .appFunction) = some .appFunction
    exact NumberedNumericStepSupportProof.positionRoundTrip .appFunction
  cases hd : decodePositions values <;>
    simp [decodePath, hp, hv, decodePositions, hposition, hd]

theorem actualCertificateDecoderLift : ApplicationStepGuardTargets.ActualCertificateDecoderLift := by
  intro certificate
  have hposition : positionNumber .appFunction = 2 := rfl
  simp [liftStep, decodeStepCertificate, hposition, actualPathDecoderLift (Nat.unpair certificate).1,
    Option.map_map, Function.comp_def, liftCertificate]

theorem actualRawCodeIdentity : ApplicationStepGuardTargets.ActualRawCodeIdentity := by
  intro n arity symbols S Gamma table sigma tau q r a certificate
  simp only [stepCodeTest, liftCertificate,
    NumberedFocusCodeSupportProof.focusCode_cons, descendCode, Option.bind_some,
    NumberedFocusCodeSupportProof.replaceCode_app]
  cases hf : focusCode certificate.path Gamma (.arrow sigma tau) q with
  | none => simp [hf]
  | some focused =>
    cases hr : rawPackedDecode n arity focused.1 certificate.replacement with
    | none => simp [hf, hr]
    | some replacement =>
      cases he : replaceCode certificate.path Gamma (.arrow sigma tau) q replacement.2 <;>
        simp [hf, hr, he]

theorem actualSourceUniverseDecomposition :
    ApplicationStepGuardTargets.ActualSourceUniverseDecomposition := by
  intro n arity symbols S Gamma sigma tau q a
  constructor
  · rintro ⟨⟨ht, hqt, hat⟩, hqh, hah⟩
    exact ⟨ht, ⟨hqt, hqh⟩, ⟨hat, hah⟩⟩
  · rintro ⟨ht, ⟨hqt, hqh⟩, ⟨hat, hah⟩⟩
    exact ⟨⟨ht, hqt, hat⟩, hqh, hah⟩

theorem actualTypedNumericIdentity : ApplicationStepGuardTargets.ActualTypedNumericIdentity := by
  intro n arity symbols S Gamma table sigma tau q r a certificate hq ha ht
  have hqa := (actualSourceUniverseDecomposition n arity symbols S Gamma sigma tau q a).mpr
    ⟨ht, hq, ha⟩
  have hdq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
    ⟨.arrow sigma tau,q⟩).mpr ⟨rfl,hq⟩
  have hdaq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    (packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma))
    ⟨tau,.app q a⟩).mpr ⟨rfl,hqa⟩
  have hdr := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
    (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma)
  have hdar := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
    (⟨tau,.app r a⟩ : Packed (Fin n) arity Gamma)
  cases hc : decodeStepCertificate certificate with
  | none =>
    simp [numericStepTest, hdq, hdaq, hdr, hdar, actualCertificateDecoderLift certificate, hc]
  | some c =>
    simpa [numericStepTest, hdq, hdaq, hdr, hdar, actualCertificateDecoderLift certificate, hc] using
      ApplicationCertificateLiftProof.actualTypedLift n arity symbols S Gamma table sigma tau q r a c

theorem actualRawEndpointIdentity : ApplicationStepGuardTargets.ActualRawEndpointIdentity := by
  intro n arity symbols S Gamma table sigma tau q r a source target argument certificate
    hsource htarget hargument ht
  have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    source ⟨.arrow sigma tau,q⟩).mp hsource
  have hr := NumberedNumericDecodingProof.packedNumericSound n arity Gamma
    target ⟨.arrow sigma tau,r⟩ htarget
  have ha := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    argument ⟨sigma,a⟩).mp hargument
  rw [← hq.1, ← hr, ← ha.1, ApplicationCertificateLiftProof.actualApplicationEncoding,
    ApplicationCertificateLiftProof.actualApplicationEncoding]
  exact actualTypedNumericIdentity n arity symbols S Gamma table sigma tau q r a certificate
    hq.2 ha.2 ht

theorem actualSubtypeClosedNumericIdentity :
    ApplicationStepGuardTargets.ActualSubtypeClosedNumericIdentity := by
  intro n arity symbols S hc Gamma table sigma tau q r a certificate hq ha
  have hft := NumberedUniverseOperationsProof.rootType (fun t => t ∈ S)
    (HeadInWindow arity symbols S) q hq
  have ht := NumberedUniverseOperationsProof.arrowCodomain (fun t => t ∈ S) hc sigma tau hft
  exact actualTypedNumericIdentity n arity symbols S Gamma table sigma tau q r a certificate hq ha ht

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardProof
