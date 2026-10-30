module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowProofCheckerProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNumericCertificateProof
open GorbowSyntax GorbowPACore GorbowProofChecker GorbowNumericCertificate

private theorem exactDecoded {α : Type} [Encodable α] (code : Nat) (a : α) :
    ((Encodable.decode (α := α) code).bind (fun b => if Encodable.encode b = code then some b else none)) = some a ↔
      Encodable.encode a = code := by
  constructor
  · intro h
    cases hd : Encodable.decode (α := α) code with
    | none => simp [hd] at h
    | some b =>
      by_cases hb : Encodable.encode b = code
      · have he : b=a := by simpa [hd,hb] using h
        simpa [he] using hb
      · simp [hd,hb] at h
  · intro h
    subst code
    simp

theorem exactDecoding : Comparators.GorbowNumericCertificate.ExactDecoding :=
  ⟨fun code raw => exactDecoded code raw,fun code lines => exactDecoded code lines⟩

theorem calibration : Comparators.GorbowNumericCertificate.Calibration := by
  intro n raw lines
  have hf := (exactDecoding.1 (Encodable.encode raw) raw).mpr rfl
  have hc := (exactDecoding.2 (certificateNumber lines) lines).mpr rfl
  simp [check,GorbowCodeConstructors.number,hf,hc]

theorem exactAcceptance : Comparators.GorbowNumericCertificate.ExactAcceptance := by
  intro n f c
  constructor
  · intro h
    cases hf : decodeFormula f with
    | none => simp [check,hf] at h
    | some raw =>
      cases hc : decodeCertificate c with
      | none => simp [check,hf,hc] at h
      | some lines =>
        exact ⟨raw,lines,((exactDecoding.1 _ _).mp hf).symm,
          ((exactDecoding.2 _ _).mp hc).symm,by simpa [check,hf,hc] using h⟩
  · rintro ⟨raw,lines,rfl,rfl,h⟩
    rw [calibration n raw lines]
    exact h

theorem coreProofEquivalence : Comparators.GorbowNumericCertificate.CoreProofEquivalence := by
  intro n f
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨raw,lines,hf,_,hv⟩ := (exactAcceptance n f c).mp hc
    obtain ⟨φ,he,hp⟩ := (GorbowProofCheckerProof.certificateEquivalence n raw).mp ⟨lines,hv⟩
    exact ⟨φ,by simpa [GorbowCodeConstructors.formulaNumber,he] using hf,hp⟩
  · rintro ⟨φ,rfl,hp⟩
    obtain ⟨lines,hv⟩ := (GorbowProofCheckerProof.certificateEquivalence n (GorbowFormulaPrefixCode.encode φ)).mpr ⟨φ,rfl,hp⟩
    refine ⟨certificateNumber lines,?_⟩
    exact (exactAcceptance n _ _).mpr ⟨GorbowFormulaPrefixCode.encode φ,lines,rfl,rfl,hv⟩

private theorem pr_guardedDecode (α : Type) [Primcodable α] :
    Primrec (fun code : Nat => (Encodable.decode (α := α) code).bind
      (fun b => if Encodable.encode b = code then some b else none)) := by
  have hb : Primrec (fun p : Nat × α => if Encodable.encode p.2 = p.1 then some p.2 else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.option_bind Primrec.decode hb.to₂
private theorem pr_decodeFormula : Primrec decodeFormula := pr_guardedDecode (List Nat)
private theorem pr_decodeCertificate : Primrec decodeCertificate := pr_guardedDecode (List Line)
private theorem pr_checkInner : Primrec (fun p : (Nat × Nat × Nat) × List Nat =>
    match decodeCertificate p.1.2.2 with
    | none => false
    | some ls => verifies p.1.1 p.2 ls) := by
  have hl : Primrec (fun p : ((Nat × Nat × Nat) × List Nat) × List Line =>
      verifies p.1.1.1 p.1.2 p.2) :=
    GorbowProofCheckerProof.uniformPrograms.2.2.2.2.2.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have h := Primrec.option_casesOn
    (pr_decodeCertificate.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const false) hl.to₂
  exact h.of_eq (fun p => by cases hx : decodeCertificate p.1.2.2 <;> simp [hx])
private theorem pr_check : Primrec (fun p : Nat × Nat × Nat => check p.1 p.2.1 p.2.2) := by
  have h := Primrec.option_casesOn (pr_decodeFormula.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const false) pr_checkInner.to₂
  exact h.of_eq (fun p => by cases hf : decodeFormula p.2.1 <;> cases hc : decodeCertificate p.2.2 <;> simp [check,hf,hc])

theorem uniformPrograms : Comparators.GorbowNumericCertificate.UniformPrograms :=
  ⟨pr_decodeFormula,pr_decodeCertificate,Primrec.encode,pr_check⟩

theorem gorbowNumericCertificate : Comparators.GorbowNumericCertificate.Target :=
  ⟨exactDecoding,calibration,exactAcceptance,coreProofEquivalence,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowNumericCertificateProof
