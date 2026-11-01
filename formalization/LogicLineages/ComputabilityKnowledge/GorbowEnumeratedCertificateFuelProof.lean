module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedCertificateFuelTargets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedCertificateFuel.Proof
open GorbowSyntax GorbowProofChecker GorbowEnumeratedProvability

private theorem axiom_mono (ax bx : List Nat → Bool)
    (hmono : ∀ raw, ax raw=true → bx raw=true) (n : Nat) (raw : List Nat) (p : Payload)
    (h : GorbowTheoryChecker.axiomCheck ax n raw p=true) :
    GorbowTheoryChecker.axiomCheck bx n raw p=true := by
  simp only [GorbowTheoryChecker.axiomCheck, decide_eq_true_eq] at h ⊢
  rcases h with ⟨h0,h1,h2,h3,hv,ha,hs⟩
  exact ⟨h0,h1,h2,h3,hv,hmono _ ha,hs⟩

private theorem line_mono (ax bx : List Nat → Bool)
    (hmono : ∀ raw, ax raw=true → bx raw=true) (history : History) (line : Line)
    (h : GorbowTheoryChecker.lineCheck ax history line=true) :
    GorbowTheoryChecker.lineCheck bx history line=true := by
  have hp : GorbowSyntaxValidation.validFormula (context line) (conclusion line)=true ∧
      GorbowTheoryChecker.ruleCheck ax history line=true := by
    simpa only [GorbowTheoryChecker.lineCheck, Bool.and_eq_true] using h
  simp only [GorbowTheoryChecker.lineCheck, hp.1, Bool.true_and]
  by_cases h4 : rule line=4
  · have ha : GorbowTheoryChecker.axiomCheck ax (context line) (conclusion line) (payload line)=true := by
      simpa only [GorbowTheoryChecker.ruleCheck,h4,if_true] using hp.2
    simpa only [GorbowTheoryChecker.ruleCheck,h4,if_true] using axiom_mono ax bx hmono _ _ _ ha
  · simpa only [GorbowTheoryChecker.ruleCheck,h4,if_false] using hp.2

private theorem fold_none (ax : List Nat → Bool) (lines : List Line) :
    lines.foldl (GorbowTheoryChecker.step ax) none=none := by
  induction lines with
  | nil => rfl
  | cons line lines ih => simpa [List.foldl,GorbowTheoryChecker.step] using ih

private theorem run_mono (ax bx : List Nat → Bool)
    (hmono : ∀ raw, ax raw=true → bx raw=true) (lines : List Line) :
    ∀ history out, GorbowTheoryChecker.run ax history lines=some out →
      GorbowTheoryChecker.run bx history lines=some out := by
  induction lines with
  | nil => intro history out h; exact h
  | cons line lines ih =>
    intro history out h
    by_cases hl : GorbowTheoryChecker.lineCheck ax history line=true
    · have hb := line_mono ax bx hmono history line hl
      have ht : GorbowTheoryChecker.run ax ((context line,conclusion line)::history) lines=some out := by
        simpa [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,hl] using h
      simpa [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,hb] using ih _ _ ht
    · simp [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,hl,fold_none] at h

private theorem verifies_mono (ax bx : List Nat → Bool)
    (hmono : ∀ raw, ax raw=true → bx raw=true) (n : Nat) (raw : List Nat) (lines : List Line)
    (h : GorbowTheoryChecker.verifies ax n raw lines=true) :
    GorbowTheoryChecker.verifies bx n raw lines=true := by
  cases hr : GorbowTheoryChecker.checkProof ax lines with
  | none => simp [GorbowTheoryChecker.verifies,hr] at h
  | some history =>
    have hb : GorbowTheoryChecker.checkProof bx lines=some history := run_mono ax bx hmono lines [] history hr
    cases history <;> simpa [GorbowTheoryChecker.verifies,hr,hb] using h

private theorem numeric_mono (ax bx : List Nat → Bool)
    (hmono : ∀ raw, ax raw=true → bx raw=true) (n formula certificate : Nat)
    (h : GorbowTheoryNumericCertificate.check ax n formula certificate=true) :
    GorbowTheoryNumericCertificate.check bx n formula certificate=true := by
  cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula with
  | none => simp [GorbowTheoryNumericCertificate.check,hf] at h
  | some raw =>
    cases hc : GorbowNumericCertificate.decodeCertificate certificate with
    | none => simp [GorbowTheoryNumericCertificate.check,hf,hc] at h
    | some lines =>
      have hv : GorbowTheoryChecker.verifies ax n raw lines=true := by
        simpa [GorbowTheoryNumericCertificate.check,hf,hc] using h
      simpa [GorbowTheoryNumericCertificate.check,hf,hc] using verifies_mono ax bx hmono n raw lines hv

theorem certificateFuelMonotonicity : Targets.CertificateFuelMonotonicity := by
  intro c s t hst n formula certificate h
  apply numeric_mono (axiomCheck (c,s)) (axiomCheck (c,t)) _ n formula certificate h
  intro raw hr
  simp only [axiomCheck,decide_eq_true_eq] at hr ⊢
  exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr hr))

theorem modusPonensMaxFuel : Targets.ModusPonensMaxFuel := by
  intro c s t n a b ci ca hi ha
  exact GorbowTheoryCertificateOperationsProof.numericModusPonens (axiomCheck (c,max s t)) n a b ci ca
    (certificateFuelMonotonicity c s (max s t) (le_max_left s t) n _ ci hi)
    (certificateFuelMonotonicity c t (max s t) (le_max_right s t) n _ ca ha)

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedCertificateFuel.Proof
