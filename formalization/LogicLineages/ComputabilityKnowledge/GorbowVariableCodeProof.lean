module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowVariableCode
public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowVariableCodeProof
open GorbowSyntax GorbowCodeConstructors GorbowVariableCode

theorem actualCalibration : Comparators.GorbowVariableCode.ActualCalibration := fun _ _ => rfl

theorem injection : Comparators.GorbowVariableCode.Injection := by
  intro i j h
  have he : variableCode i=variableCode j := Encodable.encode_injective h
  simpa [variableCode] using he

private theorem rawShape (raw : List Nat) (h : raw.length=2 ∧ raw.getD 0 1=0) :
    raw=variableCode (raw.getD 1 0) := by
  cases raw with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => simp at h
    | cons b bs =>
      have hl : bs.length=0 := by simpa using h.1
      have he : bs=[] := List.length_eq_zero_iff.mp hl
      subst bs
      have ha : a=0 := h.2
      subst a
      rfl

private theorem decodeAt (i : Nat) : decodeVariable (variableNumber i)=some i := by
  have hd := (GorbowNumericCertificateProof.exactDecoding.1 (variableNumber i) (variableCode i)).mpr rfl
  simp [decodeVariable,hd,variableCode]

theorem exactDecoding : Comparators.GorbowVariableCode.ExactDecoding := by
  intro code i
  constructor
  · intro h
    cases hd : GorbowNumericCertificate.decodeFormula code with
    | none => simp [decodeVariable,hd] at h
    | some raw =>
      simp only [decodeVariable,hd,bind,Option.bind_some] at h
      split at h
      · rename_i hg
        have hi := Option.some.inj h
        have he := rawShape raw hg
        rw [hi] at he
        have hc := (GorbowNumericCertificateProof.exactDecoding.1 code raw).mp hd
        simpa [variableNumber,number,he] using hc.symm
      · simp at h
  · rintro rfl
    exact decodeAt i

theorem exactDomain : Comparators.GorbowVariableCode.ExactDomain := by
  intro code
  cases h : decodeVariable code with
  | none =>
    simp only [isVariableCode,h,Option.isSome_none,Bool.false_eq_true,false_iff,not_exists]
    intro i hi
    have hh := (exactDecoding code i).mpr hi
    rw [h] at hh
    contradiction
  | some i =>
    simp only [isVariableCode,h,Option.isSome_some,true_iff]
    exact ⟨i,(exactDecoding code i).mp h⟩

theorem malformedRejection : Comparators.GorbowVariableCode.MalformedRejection := by
  intro code
  cases h : decodeVariable code with
  | none =>
    simp only [true_iff]
    rintro ⟨i,hi⟩
    have hh := (exactDecoding code i).mpr hi
    rw [h] at hh
    contradiction
  | some i =>
    have hi := (exactDecoding code i).mp h
    simp only [Option.some_ne_none,false_iff,not_not]
    exact ⟨i,hi⟩

private theorem pr_number : Primrec variableNumber :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2.comp GorbowCodeConstructorsProof.uniformPrograms.1
private theorem pr_body : Primrec (fun raw : List Nat =>
    if raw.length=2 ∧ raw.getD 0 1=0 then some (raw.getD 1 0) else none) := by
  have hl : PrimrecPred (fun raw : List Nat => raw.length=2) := Primrec.eq.comp Primrec.list_length (Primrec.const 2)
  have hz := Primrec.eq.comp ((Primrec.list_getD 1).comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
  have hi := Primrec.option_some.comp ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 1))
  exact Primrec.ite (hl.and hz) hi (Primrec.const none)
private theorem pr_decode : Primrec decodeVariable :=
  Primrec.option_bind GorbowNumericCertificateProof.uniformPrograms.1 (pr_body.comp Primrec.snd).to₂

theorem uniformPrograms : Comparators.GorbowVariableCode.UniformPrograms :=
  ⟨pr_number,pr_decode,Primrec.option_isSome.comp pr_decode⟩
theorem gorbowVariableCode : Comparators.GorbowVariableCode.Target :=
  ⟨actualCalibration,injection,exactDecoding,exactDomain,malformedRejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowVariableCodeProof
