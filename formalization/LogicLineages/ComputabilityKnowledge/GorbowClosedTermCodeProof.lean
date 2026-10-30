module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedTermCode
public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowClosedTermCodeProof
open GorbowSyntax GorbowStandardInstances GorbowClosedTermCode GorbowCodeConstructors

theorem closedTokenCalibration : Comparators.GorbowClosedTermCode.ClosedTokenCalibration := by
  intro t
  induction t with
  | var i => exact Fin.elim0 i
  | zero => simp [GorbowTermPrefixCode.encode]; exact ArithmeticTerm.zero
  | succ t ih =>
    simp only [GorbowTermPrefixCode.encode,List.all_cons,decide_true,Bool.true_and]
    constructor
    · intro h; exact ArithmeticTerm.succ (ih.mp h)
    · intro h; cases h with | succ h => exact ih.mpr h
  | add t u ht hu =>
    simp only [GorbowTermPrefixCode.encode,List.all_cons,List.all_append,show decide (3≠5)=true from rfl,Bool.true_and,Bool.and_eq_true]
    constructor
    · rintro ⟨h₁,h₂⟩; exact ArithmeticTerm.add (ht.mp h₁) (hu.mp h₂)
    · intro h; cases h with | add h₁ h₂ => exact ⟨ht.mpr h₁,hu.mpr h₂⟩
  | mul t u ht hu =>
    simp only [GorbowTermPrefixCode.encode,List.all_cons,List.all_append,show decide (4≠5)=true from rfl,Bool.true_and,Bool.and_eq_true]
    constructor
    · rintro ⟨h₁,h₂⟩; exact ArithmeticTerm.mul (ht.mp h₁) (hu.mp h₂)
    · intro h; cases h with | mul h₁ h₂ => exact ⟨ht.mpr h₁,hu.mpr h₂⟩
  | universalFunction t ih =>
    simp only [GorbowTermPrefixCode.encode,List.all_cons,ne_eq,not_true_eq_false,decide_false,Bool.false_and,Bool.false_eq_true,false_iff]
    intro h; cases h

private theorem validEncode (t : Term 0) : GorbowSyntaxValidation.validTerm 0 (GorbowTermPrefixCode.encode t)=true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.1 0 _).mpr
    ⟨t,(GorbowTermPrefixCodeProof.decoderExact 0 _ t).mpr rfl⟩

theorem exactRawArithmetic : Comparators.GorbowClosedTermCode.ExactRawArithmetic := by
  intro raw
  simp only [arithmeticRaw,Bool.and_eq_true]
  constructor
  · rintro ⟨hv,ha⟩
    obtain ⟨t,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 0 raw).mp hv
    have he := (GorbowTermPrefixCodeProof.decoderExact 0 raw t).mp ht
    subst raw
    exact ⟨t,rfl,(closedTokenCalibration t).mp ha⟩
  · rintro ⟨t,rfl,ht⟩
    exact ⟨validEncode t,(closedTokenCalibration t).mpr ht⟩

private theorem decodeNumber (raw : List Nat) : GorbowNumericCertificate.decodeFormula (number raw)=some raw :=
  (GorbowNumericCertificateProof.exactDecoding.1 _ _).mpr rfl

theorem exactNumericDomains : Comparators.GorbowClosedTermCode.ExactNumericDomains := by
  constructor
  · intro code
    constructor
    · intro h
      cases hd : GorbowNumericCertificate.decodeFormula code with
      | none => simp [fullTermCode,hd] at h
      | some raw =>
        have hv : GorbowSyntaxValidation.validTerm 0 raw=true := by simpa [fullTermCode,hd] using h
        obtain ⟨t,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 0 raw).mp hv
        have he := (GorbowTermPrefixCodeProof.decoderExact 0 raw t).mp ht
        have hc := (GorbowNumericCertificateProof.exactDecoding.1 code raw).mp hd
        exact ⟨t,by simpa [termNumber,number,he] using hc.symm⟩
    · rintro ⟨t,rfl⟩
      simpa [fullTermCode,termNumber,decodeNumber] using validEncode t
  · intro code
    constructor
    · intro h
      cases hd : GorbowNumericCertificate.decodeFormula code with
      | none => simp [arithmeticTermCode,hd] at h
      | some raw =>
        have hv : arithmeticRaw raw=true := by simpa [arithmeticTermCode,hd] using h
        obtain ⟨t,he,ht⟩ := (exactRawArithmetic raw).mp hv
        have hc := (GorbowNumericCertificateProof.exactDecoding.1 code raw).mp hd
        exact ⟨t,by simpa [termNumber,number,he] using hc.symm,ht⟩
    · rintro ⟨t,rfl,ht⟩
      have h := (exactRawArithmetic _).mpr ⟨t,rfl,ht⟩
      simpa [arithmeticTermCode,termNumber,decodeNumber] using h

theorem numeralCoverage : Comparators.GorbowClosedTermCode.NumeralCoverage := by
  intro k
  exact ⟨(exactNumericDomains.1 _).mpr ⟨_,rfl⟩,
    (exactNumericDomains.2 _).mpr ⟨_,rfl,GorbowStandardInstancesProof.arithmeticNumerals 0 k⟩⟩
theorem inclusion : Comparators.GorbowClosedTermCode.Inclusion := by
  intro code h
  obtain ⟨t,ht,ha⟩ := (exactNumericDomains.2 code).mp h
  exact (exactNumericDomains.1 code).mpr ⟨t,ht⟩

private theorem pr_valid : Primrec (fun raw : List Nat => GorbowSyntaxValidation.validTerm 0 raw) :=
  GorbowSyntaxValidationProof.uniformPrograms.2.2.2.1.comp ((Primrec.const 0).pair Primrec.id)
private theorem pr_all : Primrec (fun raw : List Nat => raw.all (fun tag => decide (tag≠5))) := by
  have hp : PrimrecRel (fun tag : Nat => fun _ : Unit => tag≠5) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 5)).not
  have h := hp.forall_mem_list.decide.comp Primrec.id (Primrec.const ())
  apply h.of_eq
  intro raw
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.all_eq_true,id_eq]
private theorem pr_arithmeticRaw : Primrec arithmeticRaw := Primrec.and.comp pr_valid pr_all
private theorem pr_fullTermCode : Primrec fullTermCode := by
  have h := Primrec.option_casesOn GorbowNumericCertificateProof.uniformPrograms.1 (Primrec.const false) (pr_valid.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by cases hd : GorbowNumericCertificate.decodeFormula code <;> simp [fullTermCode,hd])
private theorem pr_arithmeticTermCode : Primrec arithmeticTermCode := by
  have h := Primrec.option_casesOn GorbowNumericCertificateProof.uniformPrograms.1 (Primrec.const false) (pr_arithmeticRaw.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by cases hd : GorbowNumericCertificate.decodeFormula code <;> simp [arithmeticTermCode,hd])

theorem uniformPrograms : Comparators.GorbowClosedTermCode.UniformPrograms :=
  ⟨pr_arithmeticRaw,pr_fullTermCode,pr_arithmeticTermCode⟩
theorem gorbowClosedTermCode : Comparators.GorbowClosedTermCode.Target :=
  ⟨closedTokenCalibration,exactRawArithmetic,exactNumericDomains,numeralCoverage,inclusion,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowClosedTermCodeProof
