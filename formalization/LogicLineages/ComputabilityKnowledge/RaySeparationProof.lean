module

public import LogicLineages.ComputabilityKnowledge.Comparators.RaySeparation
public import LogicLineages.ComputabilityKnowledge.RayFamilyClosureProof
public import LogicLineages.ComputabilityKnowledge.RayHeightInductionProof
public import LogicLineages.ComputabilityKnowledge.RayCodeEvaluationProof

@[expose] public section

/-! External completion of source paper02 lem:ray after exact final target
freeze. All original heterogeneous family members, recursive keys, and zeros
share literal computed weights, threshold, and signs. No missing supplier is
introduced as a premise; all imported exact suppliers were checked first. -/
namespace LogicLineages.ComputabilityKnowledge.RaySeparationProof

open ExponentialNormalForm ExponentialHereditaryCodec
open RayFamilyClosure RayCoefficientCollection RayUniformBounds RayHeightInduction
open RaySeparation

theorem actualClosedFamily : Comparators.RaySeparation.ActualClosedFamily := by
  intro d roots hroots
  have hm := RayFamilyClosureProof.originalMembersAndZero d roots
  exact ⟨hm.1, hm.2.1, RayFamilyClosureProof.closureBoundsAndValidity d roots hroots,
    RayFamilyClosureProof.actualSupportClosure d roots hroots⟩

theorem positiveEffectiveRay : Comparators.RaySeparation.PositiveEffectiveRay := by
  intro d roots
  have hp := RayCoefficientCollectionProof.commonPositiveRay d (maxHeight roots) (liftedFamily d roots)
  have ht : 4 ≤ threshold d roots := (le_max_left 4 _).trans (le_max_right _ _)
  refine ⟨hp.1, by omega, fun i => ⟨(hp.2.2 i).1, ?_⟩⟩
  intro t hT
  exact Nat.mul_pos (hp.2.2 i).1 (by omega)

private theorem map_mul_getD (xs : List Nat) (t i : Nat) :
    (xs.map (fun a => a * t)).getD i 0 = xs.getD i 0 * t := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

private theorem evaluation_original (d : Nat) (roots : List HeightCode) (p : HeightCode) (t : Nat) :
    RayCodeEvaluation.evalCode d p.1 p.2 (rayList d roots t) = originalValue d roots p t := by
  rw [RayCodeEvaluationProof.literalHereditaryEvaluation]
  congr 1
  funext i
  exact map_mul_getD (weights d roots) t i.val

private theorem lifted_value (d : Nat) (roots : List HeightCode) (hroots : SourceFamily d roots)
    (p : HeightCode) (hp : p ∈ closedFamily d roots) (t : Nat) :
    rayValue d (maxHeight roots) (liftedFamily d roots) (maxHeight roots)
      (formDecode d (maxHeight roots) (liftCode d (maxHeight roots) p)) t =
        originalValue d roots p t :=
  ((RayFamilyClosureProof.liftedOriginalSemantics d roots hroots).2 p hp).2.1 _

private theorem sign_spec (a b : Nat) :
    (if a = b then 0 else if a < b then 1 else 2) ≤ 2 ∧
    ((if a = b then 0 else if a < b then 1 else 2) = 0 ↔ a = b) ∧
    ((if a = b then 0 else if a < b then 1 else 2) = 1 ↔ a < b) ∧
    ((if a = b then 0 else if a < b then 1 else 2) = 2 ↔ b < a) := by
  by_cases he : a = b
  · simp [he]
  · by_cases hl : a < b
    · simp [he, hl, Nat.not_lt_of_gt hl]
    · have hg : b < a := by omega
      simp [he, hl, hg]

private theorem original_sign_spec (d : Nat) (roots : List HeightCode) (p q : HeightCode) :
    signCode d roots p q ≤ 2 ∧
    (signCode d roots p q = 0 ↔ originalValue d roots p (threshold d roots) =
      originalValue d roots q (threshold d roots)) ∧
    (signCode d roots p q = 1 ↔ originalValue d roots p (threshold d roots) <
      originalValue d roots q (threshold d roots)) ∧
    (signCode d roots p q = 2 ↔ originalValue d roots q (threshold d roots) <
      originalValue d roots p (threshold d roots)) := by
  simpa only [signCode, evaluation_original] using
    sign_spec (RayCodeEvaluation.evalCode d p.1 p.2 (rayList d roots (threshold d roots)))
      (RayCodeEvaluation.evalCode d q.1 q.2 (rayList d roots (threshold d roots)))

theorem computedEventualSigns : Comparators.RaySeparation.ComputedEventualSigns := by
  refine ⟨fun d roots p q => (original_sign_spec d roots p q).1, ?_⟩
  intro d roots hroots p hp q hq t ht
  have hl := RayFamilyClosureProof.liftedOriginalSemantics d roots hroots
  have hc := fun n hn => (hl.1 n hn).1
  have hw := fun n hn => (hl.1 n hn).2
  have hpm := (hl.2 p hp).1
  have hqm := (hl.2 q hq).1
  have H := RayHeightInductionProof.stableEqualityAndOrder d (maxHeight roots)
    (liftedFamily d roots) hc hw _ hpm _ hqm t ht
  have H0 := RayHeightInductionProof.stableEqualityAndOrder d (maxHeight roots)
    (liftedFamily d roots) hc hw _ hpm _ hqm (threshold d roots) le_rfl
  have Hr := RayHeightInductionProof.stableEqualityAndOrder d (maxHeight roots)
    (liftedFamily d roots) hc hw _ hqm _ hpm t ht
  have hs := original_sign_spec d roots p q
  have hpv := lifted_value d roots hroots p hp
  have hqv := lifted_value d roots hroots q hq
  simp only [hpv, hqv] at H H0 Hr
  exact ⟨hs.2.1.trans H0.1, hs.2.2.1.trans H.2.symm, hs.2.2.2.trans Hr.2.symm⟩

theorem constantFreeGap : Comparators.RaySeparation.ConstantFreeGap := by
  intro d roots hroots p hp q hq hp0 hq0 hne t ht
  have hl := RayFamilyClosureProof.liftedOriginalSemantics d roots hroots
  have hc := fun n hn => (hl.1 n hn).1
  have hw := fun n hn => (hl.1 n hn).2
  have hpm := (hl.2 p hp).1
  have hqm := (hl.2 q hq).1
  have hpg := (hl.2 p hp).2.2.trans hp0
  have hqg := (hl.2 q hq).2.2.trans hq0
  have hg := RayHeightInductionProof.constantFreeOrientedGap d (maxHeight roots)
    (liftedFamily d roots) hc hw _ hpm _ hqm hpg hqg hne t ht
  have hpv := lifted_value d roots hroots p hp
  have hqv := lifted_value d roots hroots q hq
  simp only [hpv, hqv] at hg
  have hs := original_sign_spec d roots p q
  refine ⟨fun h => hg.1 (hs.2.2.1.mp h), fun h => hg.2 ?_⟩
  have hrev := hs.2.2.2.mp h
  dsimp only [threshold] at hrev
  omega

theorem pr_weights : Primrec (fun p : Nat × List HeightCode => weights p.1 p.2) := by
  have hh : Primrec (fun p : Nat × List HeightCode => maxHeight p.2) :=
    RayFamilyClosureProof.pr_maxHeight.comp Primrec.snd
  have hf := RayFamilyClosureProof.pr_liftedFamily
  have hargs : Primrec (fun p : Nat × List HeightCode =>
      (p.1, maxHeight p.2, liftedFamily p.1 p.2)) := Primrec.fst.pair (hh.pair hf)
  exact (RayCoefficientCollectionProof.actualUniformPrograms.2.2.1.comp hargs).of_eq (fun _ => rfl)

theorem pr_threshold : Primrec (fun p : Nat × List HeightCode => threshold p.1 p.2) := by
  have hh : Primrec (fun p : Nat × List HeightCode => maxHeight p.2) :=
    RayFamilyClosureProof.pr_maxHeight.comp Primrec.snd
  have hf := RayFamilyClosureProof.pr_liftedFamily
  have hargs : Primrec (fun p : Nat × List HeightCode =>
      (p.1, maxHeight p.2, liftedFamily p.1 p.2)) := Primrec.fst.pair (hh.pair hf)
  exact (RayUniformBoundsProof.pr_commonThreshold.comp hargs).of_eq (fun _ => rfl)

theorem pr_rayList : Primrec (fun p : Nat × List HeightCode × Nat => rayList p.1 p.2.1 p.2.2) := by
  have hw : Primrec (fun p : Nat × List HeightCode × Nat => weights p.1 p.2.1) :=
    (pr_weights.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))).of_eq (fun _ => rfl)
  have ht : Primrec (fun p : Nat × List HeightCode × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  apply Primrec.list_map hw
  exact (Primrec.nat_mul.comp Primrec.snd (ht.comp Primrec.fst)).to₂

private def sampleValue (d : Nat) (roots : List HeightCode) (p : HeightCode) : Nat :=
  RayCodeEvaluation.evalCode d p.1 p.2 (rayList d roots (threshold d roots))

private theorem pr_sampleRay : Primrec (fun p : Nat × List HeightCode × HeightCode =>
    rayList p.1 p.2.1 (threshold p.1 p.2.1)) := by
  have hd : Primrec (fun p : Nat × List HeightCode × HeightCode => p.1) := Primrec.fst
  have hr : Primrec (fun p : Nat × List HeightCode × HeightCode => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht := pr_threshold.comp (hd.pair hr)
  have hargs : Primrec (fun p : Nat × List HeightCode × HeightCode =>
      (p.1, p.2.1, threshold p.1 p.2.1)) := hd.pair (hr.pair ht)
  exact (pr_rayList.comp hargs).of_eq (fun _ => rfl)

private theorem pr_sampleValue : Primrec (fun p : Nat × List HeightCode × HeightCode =>
    sampleValue p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat × List HeightCode × HeightCode => p.1) := Primrec.fst
  have hh : Primrec (fun p : Nat × List HeightCode × HeightCode => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun p : Nat × List HeightCode × HeightCode => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hargs : Primrec (fun p : Nat × List HeightCode × HeightCode =>
      (p.1, p.2.2.1, p.2.2.2, rayList p.1 p.2.1 (threshold p.1 p.2.1))) :=
    hd.pair (hh.pair (hn.pair pr_sampleRay))
  exact RayCodeEvaluationProof.pr_evalCode.comp hargs

theorem pr_signCode : Primrec (fun p : Nat × List HeightCode × HeightCode × HeightCode =>
    signCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hd : Primrec (fun p : Nat × List HeightCode × HeightCode × HeightCode => p.1) := Primrec.fst
  have hr : Primrec (fun p : Nat × List HeightCode × HeightCode × HeightCode => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : Nat × List HeightCode × HeightCode × HeightCode => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq : Primrec (fun p : Nat × List HeightCode × HeightCode × HeightCode => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ha := pr_sampleValue.comp (hd.pair (hr.pair hp))
  have hb := pr_sampleValue.comp (hd.pair (hr.pair hq))
  exact Primrec.ite (Primrec.eq.comp ha hb) (Primrec.const 0)
    (Primrec.ite (Primrec.nat_lt.comp ha hb) (Primrec.const 1) (Primrec.const 2))

theorem actualUniformPrograms : Comparators.RaySeparation.ActualUniformPrograms :=
  ⟨pr_weights, pr_threshold, pr_rayList, pr_signCode⟩

theorem raySeparation : Comparators.RaySeparation.Target :=
  ⟨actualClosedFamily, positiveEffectiveRay, computedEventualSigns, constantFreeGap,
    actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.RaySeparationProof
