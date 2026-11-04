module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecTargets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecSupportProof
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedNumericCarrier NumberedDirectCertificate NumberedSelectCertificate NumberedCopyCertificate
open NumberedMultisetNumeric NumberedNumericMul NumberedNumericRoot NumberedNumericRootPrimrec

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

theorem outputNumberCalibration {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (output : Option (Packed (Fin n) arity Gamma)) (target : Nat) :
    outputNumberTest output target =
      (decodePackedNumber n arity Gamma target).any (fun r => decide (output = some r)) := by
  cases output with
  | none => cases decodePackedNumber n arity Gamma target <;> simp [outputNumberTest]
  | some q =>
    cases hd : decodePackedNumber n arity Gamma target with
    | none =>
      have hn : packedNumber q ≠ target := by
        intro he
        have hr := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma q
        rw [he, hd] at hr
        contradiction
      simp [outputNumberTest, hn]
    | some r =>
      have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma target r hd
      have hsame : packedNumber q = target ↔ q = r := by
        rw [← he]
        exact (NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma).eq_iff
      simp [outputNumberTest, hsame]

theorem directNumericCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (rule : DirectRule)
    (source target : Nat) :
    directNumericTest n arity symbols S Gamma rule source target =
      match decodeUniverse n arity symbols S Gamma source, decodePackedNumber n arity Gamma target with
      | some q, some r => decide (directTarget arity Gamma rule q = some r)
      | _, _ => false := by
  unfold directNumericTest
  simp only [outputNumberCalibration]
  cases decodeUniverse n arity symbols S Gamma source <;>
    cases decodePackedNumber n arity Gamma target <;> rfl

theorem selectNumericCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma types : List Ty) (index source target : Nat) :
    selectNumericTest n arity symbols S Gamma types index source target =
      match decodeUniverse n arity symbols S Gamma source, decodePackedNumber n arity Gamma target with
      | some q, some r => decide (selectTarget arity Gamma types index q = some r)
      | _, _ => false := by
  unfold selectNumericTest
  simp only [outputNumberCalibration]
  cases decodeUniverse n arity symbols S Gamma source <;>
    cases decodePackedNumber n arity Gamma target <;> rfl

theorem copyNumericCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (source target certificate : Nat) :
    copyCertificateTest n arity symbols S Gamma table source target certificate =
      match decodeUniverse n arity symbols S Gamma source, decodePackedNumber n arity Gamma target,
          decodeHeadNumber n certificate with
      | some q, some r, some head =>
          decide (copyTarget arity symbols S table Gamma (NumberedAuxiliaryDecoding.decodeHead head) q = some r)
      | _, _, _ => false := by
  have hexpand : copyCertificateTest n arity symbols S Gamma table source target certificate =
      (decodeUniverse n arity symbols S Gamma source).any (fun q =>
        (decodeHeadNumber n certificate).any (fun head =>
          outputNumberTest
            (copyTarget arity symbols S table Gamma (NumberedAuxiliaryDecoding.decodeHead head) q) target)) := by
    unfold copyCertificateTest
    cases decodeUniverse n arity symbols S Gamma source with
    | none => cases decodeHeadNumber n certificate <;> rfl
    | some q =>
      cases decodeHeadNumber n certificate with
      | none => rfl
      | some head =>
        simp only [Option.any_some, outputNumberTest]
        cases copyTarget arity symbols S table Gamma (NumberedAuxiliaryDecoding.decodeHead head) q <;> rfl
  rw [hexpand]
  simp only [outputNumberCalibration]
  cases decodeUniverse n arity symbols S Gamma source <;>
    cases decodePackedNumber n arity Gamma target <;>
      cases decodeHeadNumber n certificate <;> rfl

theorem rootDispatchCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (source target certificate : Nat) :
    rootDispatch n arity symbols S Gamma table source target certificate =
      numericRootTest n arity symbols S Gamma table source target certificate := by
  unfold rootDispatch
  generalize hparts : Nat.unpair certificate = parts
  rcases parts with ⟨tag, payload⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | tag
  · simp only [directNumericCalibration, numericRootTest, decodeSelector, hparts]
    cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;> rfl
  · cases payload <;>
      simp only [directNumericCalibration, numericRootTest, decodeSelector, hparts]
    all_goals cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;> rfl
  · cases payload <;>
      simp only [directNumericCalibration, numericRootTest, decodeSelector, hparts]
    all_goals cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;> rfl
  · cases payload <;>
      simp only [directNumericCalibration, numericRootTest, decodeSelector, hparts]
    all_goals cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;> rfl
  · simp only [selectNumericCalibration, numericRootTest, decodeSelector, hparts]
    cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;>
        cases decodeTypes (Nat.unpair payload).1 <;> rfl
  · simp only [copyNumericCalibration, numericRootTest, decodeSelector, hparts]
    cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;>
        cases decodeHeadNumber n payload <;> rfl
  · simp only [numericMulTest, numericRootTest, decodeSelector, hparts]
    cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;>
        cases decodeCertificate n arity Gamma payload <;> rfl
  · simp only [numericRootTest, decodeSelector, hparts]
    cases decodeUniverse n arity symbols S Gamma source <;>
      cases decodePackedNumber n arity Gamma target <;> rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecSupportProof
