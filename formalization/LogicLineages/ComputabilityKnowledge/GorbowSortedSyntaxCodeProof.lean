module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSyntaxCode
public import LogicLineages.ComputabilityKnowledge.GorbowVariableCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
open GorbowSyntax GorbowSortedSyntaxCode

theorem tags : Comparators.GorbowSortedSyntaxCode.Tags := by
  refine ⟨?_,?_,?_⟩
  · intro a b h; unfold tagFormula at h; omega
  · intro a b h; unfold tagTerm at h; omega
  · intro a b h; unfold tagFormula tagTerm at h; omega

theorem encodingEquality : Comparators.GorbowSortedSyntaxCode.EncodingEquality := by
  constructor
  · intro n m φ ψ
    constructor
    · intro h
      exact Encodable.encode_injective (tags.1 h)
    · intro h
      exact congrArg tagFormula (congrArg GorbowCodeConstructors.number h)
  · intro n m t u
    constructor
    · intro h
      exact Encodable.encode_injective (tags.2.1 h)
    · intro h
      exact congrArg tagTerm (congrArg GorbowCodeConstructors.number h)

theorem actualInjection : Comparators.GorbowSortedSyntaxCode.ActualInjection := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n φ ψ h
    exact GorbowFormulaPrefixCodeProof.encodingInjective n ((encodingEquality.1 n n φ ψ).mp h)
  · intro n t u h
    exact GorbowTermPrefixCodeProof.encodingInjective n ((encodingEquality.2 n n t u).mp h)
  · intro n m φ t
    exact tags.2.2 _ _
  · intro i j h
    exact GorbowVariableCodeProof.injection (tags.2.1 h)

theorem exactRawDecoding : Comparators.GorbowSortedSyntaxCode.ExactRawDecoding := by
  constructor
  · intro code raw
    constructor
    · intro h
      unfold decodeFormulaRaw at h
      split at h
      · rename_i hp
        have he := (GorbowNumericCertificateProof.exactDecoding.1 (code/2) raw).mp h
        change code=2*GorbowCodeConstructors.number raw
        change GorbowCodeConstructors.number raw=code/2 at he
        omega
      · simp at h
    · rintro rfl
      have hp : formulaRawNumber raw%2=0 := by unfold formulaRawNumber tagFormula; omega
      have hd : formulaRawNumber raw/2=GorbowCodeConstructors.number raw := by unfold formulaRawNumber tagFormula; omega
      rw [decodeFormulaRaw,if_pos hp,hd]
      exact (GorbowNumericCertificateProof.exactDecoding.1 _ _).mpr rfl
  · intro code raw
    constructor
    · intro h
      unfold decodeTermRaw at h
      split at h
      · rename_i hp
        have he := (GorbowNumericCertificateProof.exactDecoding.1 (code/2) raw).mp h
        change code=2*GorbowCodeConstructors.number raw+1
        change GorbowCodeConstructors.number raw=code/2 at he
        omega
      · simp at h
    · rintro rfl
      have hp : termRawNumber raw%2=1 := by unfold termRawNumber tagTerm; omega
      have hd : termRawNumber raw/2=GorbowCodeConstructors.number raw := by unfold termRawNumber tagTerm; omega
      rw [decodeTermRaw,if_pos hp,hd]
      exact (GorbowNumericCertificateProof.exactDecoding.1 _ _).mpr rfl

private theorem variableExact (code i : Nat) : decodeVariable code=some i ↔ code=variableNumber i := by
  constructor
  · intro h
    unfold decodeVariable at h
    split at h
    · rename_i hp
      have he := (GorbowVariableCodeProof.exactDecoding (code/2) i).mp h
      change code=2*GorbowVariableCode.variableNumber i+1
      omega
    · simp at h
  · rintro rfl
    have hp : variableNumber i%2=1 := by unfold variableNumber tagTerm; omega
    have hd : variableNumber i/2=GorbowVariableCode.variableNumber i := by unfold variableNumber tagTerm; omega
    rw [decodeVariable,if_pos hp,hd]
    exact (GorbowVariableCodeProof.exactDecoding _ i).mpr rfl

private theorem variableDomain (code : Nat) : isVariableCode code=true ↔ ∃ i,code=variableNumber i := by
  cases h : decodeVariable code with
  | none =>
    simp only [isVariableCode,h,Option.isSome_none,Bool.false_eq_true,false_iff,not_exists]
    intro i hi
    have he := (variableExact code i).mpr hi
    rw [h] at he
    contradiction
  | some i =>
    simp only [isVariableCode,h,Option.isSome_some,true_iff]
    exact ⟨i,(variableExact code i).mp h⟩

theorem actualCalibration : Comparators.GorbowSortedSyntaxCode.ActualCalibration :=
  ⟨fun _ _ => rfl,fun n φ => (exactRawDecoding.1 _ _).mpr rfl,
    fun n t => (exactRawDecoding.2 _ _).mpr rfl,variableExact,variableDomain⟩

theorem quoteSemantics : Comparators.GorbowSortedSyntaxCode.QuoteSemantics :=
  ⟨fun _ _ φ I ρ => numeral_realize I ρ (formulaCode φ),
    fun _ _ t I ρ => numeral_realize I ρ (termCode t)⟩

private theorem pr_formulaTag : Primrec tagFormula := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
private theorem pr_termTag : Primrec tagTerm := Primrec.succ.comp pr_formulaTag
private theorem pr_div : Primrec (fun code : Nat => code/2) := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
private theorem pr_parity (k : Nat) : PrimrecPred (fun code : Nat => code%2=k) :=
  Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const k)
private theorem pr_decodeFormula : Primrec decodeFormulaRaw :=
  Primrec.ite (pr_parity 0) (GorbowNumericCertificateProof.uniformPrograms.1.comp pr_div) (Primrec.const none)
private theorem pr_decodeTerm : Primrec decodeTermRaw :=
  Primrec.ite (pr_parity 1) (GorbowNumericCertificateProof.uniformPrograms.1.comp pr_div) (Primrec.const none)
private theorem pr_decodeVariable : Primrec decodeVariable :=
  Primrec.ite (pr_parity 1) (GorbowVariableCodeProof.uniformPrograms.2.1.comp pr_div) (Primrec.const none)

theorem uniformPrograms : Comparators.GorbowSortedSyntaxCode.UniformPrograms :=
  ⟨pr_formulaTag,pr_termTag,
    pr_formulaTag.comp GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2,
    pr_termTag.comp GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2,
    pr_termTag.comp GorbowVariableCodeProof.uniformPrograms.1,
    pr_decodeFormula,pr_decodeTerm,pr_decodeVariable,Primrec.option_isSome.comp pr_decodeVariable⟩
theorem gorbowSortedSyntaxCode : Comparators.GorbowSortedSyntaxCode.Target :=
  ⟨tags,encodingEquality,actualInjection,exactRawDecoding,actualCalibration,quoteSemantics,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
