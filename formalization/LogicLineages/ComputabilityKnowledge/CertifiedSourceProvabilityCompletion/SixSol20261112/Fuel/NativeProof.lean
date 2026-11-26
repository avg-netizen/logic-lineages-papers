module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedCertificateFuelProof

@[expose] public section
/-! External calibration of the explicit AST. These are deliberately separate
from the ordinary source derivations of fuel persistence. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.NativeProof
open GorbowPRProgram GorbowPublishedDCB List.Vector

theorem isZeroValue (k : Nat) : evaluate isZero (k ::ᵥ nil) = if k = 0 then 1 else 0 := by
  cases k <;> rfl

theorem isOneValue (k : Nat) : evaluate isOne (k ::ᵥ nil) = if k = 1 then 1 else 0 := by
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem orValue (k x : Nat) : evaluate leftOr (k ::ᵥ x ::ᵥ nil) = if k = 0 then x else k := by
  cases k <;> rfl

theorem baseValue (q0 : Program 5) (index context formula cert : Nat) :
    evaluate (base q0) (index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) =
      if evaluate q0 (inputs index 0 context formula cert) = 1 then 1 else 0 := by
  change evaluate isOne (evaluate q0 (inputs index 0 context formula cert) ::ᵥ nil) = _
  exact isOneValue _

theorem stepValue (q0 : Program 5) (counter previous index context formula cert : Nat) :
    evaluate (step q0) (counter ::ᵥ previous ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) =
      if previous = 0 then
        (if evaluate q0 (inputs index (counter+1) context formula cert) = 1 then 1 else 0)
      else previous := by
  change evaluate leftOr (previous ::ᵥ
    evaluate isOne (evaluate q0 (inputs index (counter+1) context formula cert) ::ᵥ nil) ::ᵥ nil) = _
  rw [orValue,isOneValue]

def scan (q0 : Program 5) (index context formula cert : Nat) : Nat → Nat
  | 0 => if evaluate q0 (inputs index 0 context formula cert) = 1 then 1 else 0
  | k+1 => if scan q0 index context formula cert k = 0 then
      (if evaluate q0 (inputs index (k+1) context formula cert) = 1 then 1 else 0)
    else scan q0 index context formula cert k

theorem accumulatorValue (q0 : Program 5) (index context formula cert fuel : Nat) :
    evaluate (accumulator q0) (fuel ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) =
      scan q0 index context formula cert fuel := by
  induction fuel with
  | zero => exact baseValue q0 index context formula cert
  | succ fuel ih =>
      change evaluate (step q0) (fuel ::ᵥ
        evaluate (accumulator q0) (fuel ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) ::ᵥ
        index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) = _
      rw [stepValue,ih]
      rfl

theorem verifierValue (q0 : Program 5) (index fuel context formula cert : Nat) :
    evaluate (verifier q0) (inputs index fuel context formula cert) =
      scan q0 index context formula cert fuel := by
  change evaluate (accumulator q0) (fuel ::ᵥ index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil) = _
  exact accumulatorValue q0 index context formula cert fuel

theorem scanSpecification (q0 : Program 5) (index context formula cert : Nat) :
    ∀ fuel,
      (scan q0 index context formula cert fuel = 1 ↔
        ∃ t, t ≤ fuel ∧ evaluate q0 (inputs index t context formula cert) = 1) ∧
      (scan q0 index context formula cert fuel = 0 ∨ scan q0 index context formula cert fuel = 1) := by
  intro fuel
  induction fuel with
  | zero =>
      by_cases hv : evaluate q0 (inputs index 0 context formula cert) = 1
      · refine ⟨?_, Or.inr (by simp only [scan,hv,if_true])⟩
        constructor
        · intro _; exact ⟨0,le_rfl,hv⟩
        · intro _; simp only [scan,hv,if_true]
      · refine ⟨?_, Or.inl (by simp only [scan,hv,if_false])⟩
        constructor
        · intro h; simp only [scan,hv,if_false] at h; contradiction
        · rintro ⟨t,ht,he⟩
          have hz : t = 0 := Nat.eq_zero_of_le_zero ht
          subst t
          exact False.elim (hv he)
  | succ fuel ih =>
      rcases ih.2 with hp | hp
      · have hs : scan q0 index context formula cert (fuel+1) =
            if evaluate q0 (inputs index (fuel+1) context formula cert) = 1 then 1 else 0 := by
          simp only [scan,hp,if_true]
        refine ⟨?_,?_⟩
        · constructor
          · intro h
            have hv : evaluate q0 (inputs index (fuel+1) context formula cert) = 1 := by
              by_contra hn
              rw [hs,if_neg hn] at h
              contradiction
            exact ⟨fuel+1,le_rfl,hv⟩
          · rintro ⟨t,ht,hv⟩
            by_cases hold : t ≤ fuel
            · have hx := ih.1.mpr ⟨t,hold,hv⟩
              rw [hp] at hx
              contradiction
            · have he : t = fuel+1 := by omega
              subst t
              rw [hs,if_pos hv]
        · by_cases hv : evaluate q0 (inputs index (fuel+1) context formula cert) = 1
          · exact Or.inr (by rw [hs,if_pos hv])
          · exact Or.inl (by rw [hs,if_neg hv])
      · have hs : scan q0 index context formula cert (fuel+1) = 1 := by
          simp only [scan,hp,show (1:Nat) ≠ 0 by decide,if_false]
        refine ⟨?_,Or.inr hs⟩
        constructor
        · intro _
          obtain ⟨t,ht,hv⟩ := ih.1.mp hp
          exact ⟨t,ht.trans (Nat.le_succ fuel),hv⟩
        · intro _; exact hs

theorem nativeSaturation : Targets.NativeSaturation := by
  intro q0 index fuel context formula cert
  rw [verifierValue]
  exact scanSpecification q0 index context formula cert fuel

theorem sameNumericChecker : Targets.SameNumericChecker := by
  intro q0 hq0 c fuel context formula cert
  change evaluate (verifier q0) (inputs (Encodable.encode c) fuel context formula cert) = _
  have hspec := nativeSaturation q0 (Encodable.encode c) fuel context formula cert
  have hcalibration (k : Nat) :
      evaluate q0 (inputs (Encodable.encode c) k context formula cert) =
        if GorbowEnumeratedProvability.check (c,k) context formula cert then 1 else 0 :=
    hq0 c k context formula cert
  by_cases hf : GorbowEnumeratedProvability.check (c,fuel) context formula cert = true
  · have hv : evaluate q0 (inputs (Encodable.encode c) fuel context formula cert) = 1 := by
      rw [hcalibration fuel,hf]
      rfl
    rw [hspec.1.mpr ⟨fuel,le_rfl,hv⟩,hf]
    rfl
  · have hn : evaluate (verifier q0) (inputs (Encodable.encode c) fuel context formula cert) ≠ 1 := by
      intro h
      obtain ⟨t,ht,hv⟩ := hspec.1.mp h
      have ha : GorbowEnumeratedProvability.check (c,t) context formula cert = true := by
        by_contra hbad
        rw [hcalibration t,if_neg hbad] at hv
        contradiction
      exact hf (GorbowEnumeratedCertificateFuel.Proof.certificateFuelMonotonicity
        c t fuel ht context formula cert ha)
    have hz := hspec.2.resolve_right hn
    rw [hz,if_neg hf]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.NativeProof
