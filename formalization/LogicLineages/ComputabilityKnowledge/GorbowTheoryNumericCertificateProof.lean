module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCheckerProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
open GorbowSyntax GorbowTheoryProof GorbowTheoryChecker GorbowSortedSyntaxCode
open GorbowNumericCertificate (decodeCertificate certificateNumber)
open GorbowProofChecker (Line)
open GorbowTheoryNumericCertificate

theorem calibration : Comparators.GorbowTheoryNumericCertificate.Calibration := by
  intro axCheck n raw lines
  have hf := (GorbowSortedSyntaxCodeProof.exactRawDecoding.1 (formulaRawNumber raw) raw).mpr rfl
  have hc := (GorbowNumericCertificateProof.exactDecoding.2 (certificateNumber lines) lines).mpr rfl
  simp [check,hf,hc]

theorem exactAcceptance : Comparators.GorbowTheoryNumericCertificate.ExactAcceptance := by
  intro axCheck n f c
  constructor
  · intro h
    cases hf : decodeFormulaRaw f with
    | none => simp [check,hf] at h
    | some raw =>
      cases hc : decodeCertificate c with
      | none => simp [check,hf,hc] at h
      | some lines =>
        exact ⟨raw,lines,(GorbowSortedSyntaxCodeProof.exactRawDecoding.1 _ _).mp hf,
          ((GorbowNumericCertificateProof.exactDecoding.2 _ _).mp hc).symm,by simpa [check,hf,hc] using h⟩
  · rintro ⟨raw,lines,rfl,rfl,h⟩
    rw [calibration axCheck n raw lines]
    exact h

theorem proofEquivalence : Comparators.GorbowTheoryNumericCertificate.ProofEquivalence := by
  intro axCheck n f
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨raw,lines,hf,_,hv⟩ := (exactAcceptance axCheck n f c).mp hc
    obtain ⟨φ,he,hp⟩ := (GorbowTheoryCheckerProof.certificateEquivalence axCheck n raw).mp ⟨lines,hv⟩
    exact ⟨φ,by simpa [formulaRawNumber,formulaCode,GorbowCodeConstructors.formulaNumber,he] using hf,hp⟩
  · rintro ⟨φ,rfl,hp⟩
    obtain ⟨lines,hv⟩ := (GorbowTheoryCheckerProof.certificateEquivalence axCheck n (GorbowFormulaPrefixCode.encode φ)).mpr ⟨φ,rfl,hp⟩
    refine ⟨certificateNumber lines,?_⟩
    exact (exactAcceptance axCheck n _ _).mpr ⟨GorbowFormulaPrefixCode.encode φ,lines,rfl,rfl,hv⟩

theorem malformedRejection : Comparators.GorbowTheoryNumericCertificate.MalformedRejection := by
  constructor
  · intro axCheck n f c h
    rcases h with hf | hc
    · simp [check,hf]
    · cases hf : decodeFormulaRaw f <;> simp [check,hf,hc]
  · intro axCheck n f c raw hf hv
    cases hc : decodeCertificate c with
    | none => simp [check,hf,hc]
    | some lines => simpa [check,hf,hc] using GorbowTheoryCheckerProof.malformedRejection axCheck n raw hv lines

private theorem pr_inner (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : (Nat × Nat × Nat) × List Nat =>
      match decodeCertificate p.1.2.2 with
      | none => false
      | some ls => verifies axCheck p.1.1 p.2 ls) := by
  have hl : Primrec (fun p : ((Nat × Nat × Nat) × List Nat) × List Line =>
      verifies axCheck p.1.1.1 p.1.2 p.2) :=
    (GorbowTheoryCheckerProof.uniformPrograms axCheck ha).2.2.2.2.2.2.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have h := Primrec.option_casesOn
    (GorbowNumericCertificateProof.uniformPrograms.2.1.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.const false) hl.to₂
  exact h.of_eq (fun p => by cases hx : decodeCertificate p.1.2.2 <;> simp [hx])

theorem uniformProgram : Comparators.GorbowTheoryNumericCertificate.UniformProgram := by
  intro axCheck ha
  have h := Primrec.option_casesOn
    (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.const false) (pr_inner axCheck ha).to₂
  exact h.of_eq (fun p => by cases hf : decodeFormulaRaw p.2.1 <;> cases hc : decodeCertificate p.2.2 <;> simp [check,hf,hc])

theorem gorbowTheoryNumericCertificate : Comparators.GorbowTheoryNumericCertificate.Target :=
  ⟨calibration,exactAcceptance,proofEquivalence,malformedRejection,uniformProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
