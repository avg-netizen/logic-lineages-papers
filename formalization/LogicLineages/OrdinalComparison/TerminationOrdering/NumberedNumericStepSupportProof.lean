module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedTypedFocus NumberedStepCertificate NumberedMultisetNumeric NumberedNumericStep

theorem positionRoundTrip (p : Position) : decodePosition (positionNumber p)=some p := by
  cases p <;> simp [positionNumber,decodePosition]

theorem positionSound (value : Nat) (p : Position) (h : decodePosition value=some p) : positionNumber p=value := by
  have hv := Nat.pair_unpair value
  unfold decodePosition at h
  split at h <;> try contradiction
  all_goals cases h <;> simp_all [positionNumber]

theorem positionsRoundTrip (path : List Position) : decodePositions (path.map positionNumber)=some path := by
  induction path with
  | nil => rfl
  | cons p path ih => simp [decodePositions,positionRoundTrip,ih]

theorem positionsSound (values : List Nat) : ∀ path,decodePositions values=some path → path.map positionNumber=values := by
  induction values with
  | nil => intro path h; cases h; rfl
  | cons value values ih =>
    intro path h
    cases hp : decodePosition value with
    | none => simp [decodePositions,hp] at h
    | some p =>
      cases hr : decodePositions values with
      | none => simp [decodePositions,hp,hr] at h
      | some rest =>
        simp only [decodePositions,hp,hr,Option.bind_some,Option.some.injEq] at h
        cases h
        simp [positionSound value p hp,ih rest hr]

theorem pathRoundTrip (path : List Position) : decodePath (pathNumber path)=some path := by
  simp [decodePath,pathNumber,NumberedMultisetNumericSupportProof.numbersRoundTrip,positionsRoundTrip]

theorem pathSound (value : Nat) (path : List Position) (h : decodePath value=some path) : pathNumber path=value := by
  cases hv : decodeNumbers value with
  | none => simp [decodePath,hv] at h
  | some values =>
    have hp : decodePositions values=some path := by simpa [decodePath,hv] using h
    unfold pathNumber
    rw [positionsSound values path hp]
    exact NumberedMultisetNumericSupportProof.numbersSound value values hv

theorem certificateRoundTrip (c : StepCertificate) : decodeStepCertificate (stepCertificateNumber c)=some c := by
  cases c
  simp [decodeStepCertificate,stepCertificateNumber,pathRoundTrip]

theorem certificateSound (value : Nat) (c : StepCertificate) (h : decodeStepCertificate value=some c) : stepCertificateNumber c=value := by
  simp only [decodeStepCertificate,Option.map_eq_some_iff] at h
  obtain ⟨path,hp,rfl⟩ := h
  simp [stepCertificateNumber,pathSound _ path hp]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepSupportProof
