module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetSupportProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedMarkCertificate
open NumberedNumericDecoding NumberedMultisetCertificate NumberedMultisetNumeric
open NumberedUniformPackedDecoding NumberedUniformMultiset

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

theorem rawMarkCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (label : Nat) (q : Packed (Fin n) arity Gamma) :
    rawMark label (packedCode q) = (markTarget label q).map packedCode := by
  unfold rawMark packedCode
  rw [NumberedFiniteMarkPrimrecProof.finiteMarkCodeCalibration
    (Fin n) arity Gamma q.1 label q.2]
  simp only [markTarget, Option.map_map, Function.comp_def]

theorem rawMarkSuccess (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (label : Nat) (q r : Packed (Fin n) arity Gamma) :
    rawMark label (packedCode q) = some (packedCode r) ↔ markTarget label q = some r := by
  rw [rawMarkCalibration]
  constructor
  · intro h
    obtain ⟨s, hs, hcode⟩ := Option.map_eq_some_iff.mp h
    have hsr := NumberedAuxiliaryCodingProof.packedCodeInjective (Fin n) arity Gamma hcode
    simpa only [hsr] using hs
  · intro h
    simp only [h, Option.map_some]

theorem replacementCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (removed inserted : List (Packed (Fin n) arity Gamma)) (witnesses : List MarkWitness) :
    rawReplacementTest (removed.map packedCode) (inserted.map packedCode) witnesses =
      replacementTest removed inserted witnesses := by
  induction inserted generalizing witnesses with
  | nil => cases witnesses <;> rfl
  | cons q rest ih =>
    cases witnesses with
    | nil => rfl
    | cons witness witnesses =>
      rcases witness with ⟨index, label⟩
      simp only [List.map_cons, rawReplacementTest, replacementTest, List.getElem?_map]
      cases h : removed[index]? with
      | none => simp only [Option.map_none]
      | some s =>
        simp only [Option.map_some]
        rw [ih witnesses]
        rw [Bool.decide_congr (rawMarkSuccess n arity Gamma label s q)]

theorem multisetCalibration : NumberedUniformMultisetTargets.ActualMultisetCalibration := by
  intro n arity Gamma source target certificate
  have hi := NumberedAuxiliaryCodingProof.packedCodeInjective (Fin n) arity Gamma
  have hn : certificate.removed.map packedCode ≠ [] ↔ certificate.removed ≠ [] := by
    cases certificate.removed <;> simp
  simp only [rawMultisetTest, certificateData, multisetTest, replacementCalibration,
    ← List.map_append, List.map_perm_map_iff hi, hn]

theorem packedNumbersCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (values : List Nat) :
    decodeRawPackedNumbers n arity Gamma values =
      (decodePackedNumbers n arity Gamma values).map (List.map packedCode) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [decodeRawPackedNumbers, decodePackedNumbers, ih]
    rw [NumberedUniformPackedDecodingProof.rawPackedCalibration n arity Gamma value]
    cases decodePackedNumber n arity Gamma value <;>
      cases decodePackedNumbers n arity Gamma rest <;> rfl

theorem packedListCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) :
    decodeRawPackedList n arity Gamma value =
      (decodePackedList n arity Gamma value).map (List.map packedCode) := by
  unfold decodeRawPackedList decodePackedList
  cases decodeNumbers value with
  | none => rfl
  | some values =>
    change decodeRawPackedNumbers n arity Gamma values =
      (decodePackedNumbers n arity Gamma values).map (List.map packedCode)
    exact packedNumbersCalibration n arity Gamma values

theorem certificateDecoderCalibration :
    NumberedUniformMultisetTargets.ActualCertificateDecoderCalibration := by
  intro n arity Gamma value
  unfold decodeRawCertificate decodeCertificate
  simp only [packedListCalibration]
  cases decodePackedList n arity Gamma (Nat.unpair value).1 <;>
    cases decodePackedList n arity Gamma (Nat.unpair (Nat.unpair value).2).1 <;>
    cases decodePackedList n arity Gamma (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).1 <;>
    cases decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2 <;> rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetSupportProof
