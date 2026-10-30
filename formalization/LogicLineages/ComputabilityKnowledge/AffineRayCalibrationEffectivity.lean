module

public import LogicLineages.ComputabilityKnowledge.Comparators.AffineRayCalibration
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof

@[expose] public section

/-! Genuine uniform programs for the frozen affine-ray calibration. The
mathematical slope-injectivity and eventual-comparison clauses are separate.
-/
namespace LogicLineages.ComputabilityKnowledge.AffineRayCalibrationEffectivity

open AffineRayCalibration ExponentialNormalFormCodec

private theorem pr_pow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem pr_coeffMass : Primrec (fun c : CoeffCode => c.foldr (fun x s => x + s) 0) := by
  have hstep : Primrec₂ (fun (_ : CoeffCode) (p : Nat × Nat) => p.1 + p.2) :=
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq fun _ => rfl

theorem pr_familyMass : Primrec familyMass := by
  have hstep : Primrec₂ (fun (_ : List CoeffCode) (p : CoeffCode × Nat) =>
      p.1.foldr (fun x s => x + s) 0 + p.2) :=
    (Primrec.nat_add.comp (pr_coeffMass.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq fun _ => rfl

theorem pr_rayBase : Primrec rayBase :=
  (Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.const 2) pr_familyMass)).of_eq fun _ => rfl

theorem pr_weights : Primrec (fun p : Nat × List CoeffCode => weights p.1 p.2) := by
  have hpow : Primrec₂ (fun (p : Nat × List CoeffCode) (i : Nat) => rayBase p.2 ^ i) :=
    (pr_pow.comp (pr_rayBase.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  exact (Primrec.list_map (Primrec.list_range.comp Primrec.fst) hpow).of_eq fun _ => rfl

theorem pr_cutoff : Primrec cutoff :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) pr_familyMass)
    (Primrec.const 1)).of_eq fun _ => rfl

theorem pr_slope :
    Primrec (fun p : Nat × List CoeffCode × CoeffCode => slope p.1 p.2.1 p.2.2) := by
  have hstep : Primrec₂ (fun (p : Nat × List CoeffCode × CoeffCode) (q : Nat × Nat) =>
      p.2.2.getD (q.1 + 1) 0 * rayBase p.2.1 ^ q.1 + q.2) := by
    have hcoeff : Primrec (fun x : (Nat × List CoeffCode × CoeffCode) × (Nat × Nat) =>
        x.1.2.2.getD (x.2.1 + 1) 0) :=
      (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
    have hpower : Primrec (fun x : (Nat × List CoeffCode × CoeffCode) × (Nat × Nat) =>
        rayBase x.1.2.1 ^ x.2.1) :=
      pr_pow.comp (pr_rayBase.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp Primrec.snd)
    exact (Primrec.nat_add.comp (Primrec.nat_mul.comp hcoeff hpower)
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr (Primrec.list_range.comp
    (show Primrec (fun p : Nat × List CoeffCode × CoeffCode => p.1) from Primrec.fst))
    (Primrec.const 0) hstep
  exact h.of_eq fun _ => rfl

theorem pr_rayCompare :
    Primrec (fun p : Nat × List CoeffCode × CoeffCode × CoeffCode =>
      rayCompare p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hd : Primrec (fun p : Nat × List CoeffCode × CoeffCode × CoeffCode => p.1) := Primrec.fst
  have hf : Primrec (fun p : Nat × List CoeffCode × CoeffCode × CoeffCode => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : Nat × List CoeffCode × CoeffCode × CoeffCode => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : Nat × List CoeffCode × CoeffCode × CoeffCode => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsa := pr_slope.comp (hd.pair (hf.pair ha))
  have hsb := pr_slope.comp (hd.pair (hf.pair hb))
  have hca := (Primrec.list_getD 0).comp ha (Primrec.const 0)
  have hcb := (Primrec.list_getD 0).comp hb (Primrec.const 0)
  have h := Primrec.ite (Primrec.eq.comp hsa hsb)
    (Primrec.nat_lt.comp hca hcb).decide (Primrec.nat_lt.comp hsa hsb).decide
  exact h.of_eq fun _ => rfl

theorem actualPrimitivePrograms : Comparators.AffineRayCalibration.ActualPrimitivePrograms :=
  ⟨pr_weights, pr_cutoff, pr_slope, pr_rayCompare⟩

end LogicLineages.ComputabilityKnowledge.AffineRayCalibrationEffectivity
