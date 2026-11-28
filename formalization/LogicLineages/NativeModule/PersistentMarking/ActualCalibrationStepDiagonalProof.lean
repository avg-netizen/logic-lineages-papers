module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePsiProof

@[expose] public section

/-! The base step `(1, N_B)` and the diagonal lemma for an arbitrary family of steps. The proof of
the diagonal lemma is the successor case of `upperStep`/`lowerStep` read abstractly: upper bound
by leastness in (P) with the fixed point as candidate; lower bound by closure in (P), activity of
the family members by the stall lemma, and the `N_B`-doubling argument for "the value is a limit". -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

theorem stepBase : StepBase := by
  intro Z s add mul w one pow fix h1 h2
  have infl := veblen_infl h1 h2
  refine ⟨?_, ?_⟩
  · intro ζ x hctx hx hψ
    have hend : ζ + 1 ≤ endpoint := hctx.1
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    refine psiO_least h1 h2 hend _ (crit_succ x hx) (fun η hη _ => ?_)
    have hη' : η ≤ ζ := Order.lt_add_one_iff.1 hη
    exact lt_of_le_of_lt ((psiO_mono h1 h2 hζend hη').trans hψ) (infl x)
  · intro ζ x hctx hnorm _ hx
    have hend : ζ + 1 ≤ endpoint := hctx.1
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    have hζlt : ζ < ζ + 1 := Order.lt_add_one_iff.2 le_rfl
    have hlt := psiO_closure h1 h2 hend hζlt hnorm
    obtain ⟨pc, hpc⟩ := crit_val (psiO_crit (w := w) h1 h2 hζend)
    obtain ⟨θc, hθc⟩ := crit_val (psiO_crit (w := w) h1 h2 hend)
    have c1 : Critical (veblenValue fix pow) (baseValue fix pow w) pc.val := by
      rw [hpc]
      exact psiO_crit h1 h2 hζend
    have c2 : Critical (veblenValue fix pow) (baseValue fix pow w) θc.val := by
      rw [hθc]
      exact psiO_crit h1 h2 hend
    have st := crit_step h1 h2 pc θc c1 c2 (by rw [hpc, hθc]; exact hlt)
    rw [← hθc]
    exact le_trans ((veblen_monoInfl h1 h2).1 x pc (by rw [hpc]; exact hx)) st

theorem stepDiagonal : StepDiagonal := by
  intro Z s add mul w one pow fix h1 h2 π πΩ K D hUp hLow hlt hcof hn1 hn2 hm1 hm2 hid hlim hcl
    hcrit hD
  have πΩpos : 0 < πΩ := lt_of_le_of_lt (ozl _) (hlt zeroValue)
  have ctx : ∀ (ζ : Ordinal.{0}) (a : CountableOrdinal), StepContext ζ πΩ → StepContext ζ (π a) :=
    fun ζ a hc => ⟨le_trans ((add_le_add_iff_left ζ).2 (hlt a).le) hc.1,
      fun τ hτ => hc.2 τ (lt_trans hτ (hlt a))⟩
  refine ⟨?_, ?_⟩
  · -- upper half
    intro ζ x hctx hx hψ
    have hend : ζ + πΩ ≤ endpoint := hctx.1
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    obtain ⟨hfix, hxκ, -⟩ := hD x
    have hpos : 0 < (D x).val := lt_of_le_of_lt (ozl _) hxκ
    obtain ⟨hκlim, hκcl⟩ := hcl (D x) hfix hpos
    have hΓκ : (baseValue fix pow w).val < (D x).val :=
      lt_of_le_of_lt (crit_ge_base h1 h2 hx) hxκ
    have κcrit := hcrit (D x) hfix hΓκ
    refine psiO_least h1 h2 hend _ κcrit (fun η hη hn => ?_)
    rcases le_total η ζ with h | h
    · exact lt_of_le_of_lt ((psiO_mono h1 h2 hζend h).trans hψ) hxκ
    · have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le h
      have hτ : η - ζ < πΩ := (Ordinal.sub_lt_of_le h).2 hη
      have hnorm : coefficientNorm (η - ζ) ≤ coefficientNorm η := by
        have hs := hctx.2 (η - ζ) hτ
        rw [hητ] at hs
        rw [hs]
        exact le_max_right _ _
      obtain ⟨a, b, hb, han, hτb⟩ := hcof (η - ζ) hτ
      have haκ : a.val < (D x).val := lt_of_le_of_lt (han.trans hnorm) hn
      have hbκ : b.val < (D x).val := by
        rw [hb]
        exact hκlim.add_one_lt haκ
      have hb1 : 1 ≤ b.val := by
        rw [hb]
        exact le_add_self
      have hlt' : η < ζ + π b := lt_of_eq_of_lt hητ.symm ((add_lt_add_iff_left ζ).2 hτb)
      have hcb := ctx ζ b hctx
      exact lt_of_le_of_lt
        ((psiO_mono h1 h2 hcb.1 hlt'.le).trans (hUp b hb1 ζ x hcb hx hψ)) (hκcl b x hbκ hxκ)
  · -- lower half
    intro ζ x hctx hnorm hπθ hx
    have hend : ζ + πΩ ≤ endpoint := hctx.1
    obtain ⟨θc, hθc⟩ := crit_val (psiO_crit (w := w) h1 h2 hend)
    rw [← hθc] at hnorm hπθ ⊢
    have θcrit : Critical (veblenValue fix pow) (baseValue fix pow w) θc.val := by
      rw [hθc]
      exact psiO_crit h1 h2 hend
    have θgt1 : 1 < θc.val := by
      rw [hθc]
      exact psiO_gt_one h1 h2 hend
    have closure : ∀ η : Ordinal.{0}, η < ζ + πΩ → coefficientNorm η < θc.val →
        psiO fix pow w η < θc.val := by
      intro η hη hn
      rw [hθc] at hn ⊢
      exact psiO_closure h1 h2 hend hη hn
    have ltTop : ∀ a : CountableOrdinal, ζ + π a < ζ + πΩ :=
      fun a => (add_lt_add_iff_left ζ).2 (hlt a)
    have normξ : ∀ a : CountableOrdinal, coefficientNorm (ζ + π a) =
        max (coefficientNorm ζ) (coefficientNorm (π a)) := fun a => hctx.2 (π a) (hlt a)
    have small : ∀ a : CountableOrdinal, 1 ≤ a.val → a.val < θc.val →
        max (coefficientNorm ζ) (coefficientNorm (π a)) < θc.val :=
      fun a ha1 haθ => max_lt hnorm (lt_of_le_of_lt (hn1 a ha1) (max_lt hπθ haθ))
    have below : ∀ a : CountableOrdinal, 1 ≤ a.val → a.val < θc.val →
        psiO fix pow w (ζ + π a) < θc.val := by
      intro a ha1 haθ
      refine closure _ (ltTop a) ?_
      rw [normξ a]
      exact small a ha1 haθ
    have active : ∀ a : CountableOrdinal, 1 ≤ a.val → a.val < θc.val →
        coefficientNorm ζ < psiO fix pow w (ζ + π a) ∧
        coefficientNorm (π a) < psiO fix pow w (ζ + π a) := by
      intro a ha1 haθ
      by_contra hcon
      have hM : psiO fix pow w (ζ + π a) ≤ max (coefficientNorm ζ) (coefficientNorm (π a)) := by
        rcases not_and_or.1 hcon with h | h
        · exact (not_lt.1 h).trans (le_max_left _ _)
        · exact (not_lt.1 h).trans (le_max_right _ _)
      have hstall : psiO fix pow w (ζ + πΩ) = psiO fix pow w (ζ + π a) := by
        refine psiO_stall h1 h2 hend (ltTop a).le (fun η hge hlt' => hM.trans ?_)
        have hζη : ζ ≤ η := le_self_add.trans hge
        have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le hζη
        have hτ : η - ζ < πΩ := (Ordinal.sub_lt_of_le hζη).2 hlt'
        have hle : π a ≤ η - ζ := (Ordinal.le_sub_of_le hζη).2 hge
        have hs := hctx.2 (η - ζ) hτ
        rw [hητ] at hs
        rw [hs]
        exact max_le_max le_rfl (hn2 a (η - ζ) ha1 hle hτ)
      have hθM : θc.val ≤ max (coefficientNorm ζ) (coefficientNorm (π a)) := by
        rw [hθc, hstall]
        exact hM
      exact absurd hθM (not_le.2 (small a ha1 haθ))
    have lowA : ∀ a : CountableOrdinal, 1 ≤ a.val → a.val < θc.val →
        (K a x).val ≤ psiO fix pow w (ζ + π a) := by
      intro a ha1 haθ
      obtain ⟨a1, a2⟩ := active a ha1 haθ
      exact hLow a ha1 ζ x (ctx ζ a hctx) a1 a2 hx
    have hζlt : ζ < ζ + πΩ := by
      have h := (add_lt_add_iff_left ζ).2 πΩpos
      rw [add_zero] at h
      exact h
    have hxθ : x.val < θc.val := lt_of_le_of_lt hx (closure ζ hζlt hnorm)
    have θlim : Order.IsSuccLimit θc.val := by
      rcases countable_cases θc with h0 | ⟨c, hc⟩ | hl
      · exact absurd θgt1 (by rw [h0]; exact not_lt.2 zero_le_one)
      · exfalso
        have hcθ : c.val < θc.val := by rw [hc]; exact Order.lt_add_one_iff.2 le_rfl
        have c1 : 1 ≤ c.val := by
          have h := θgt1
          rw [hc] at h
          exact Order.lt_add_one_iff.1 h
        have a := lowA c c1 hcθ
        have b := below c c1 hcθ
        rw [hc] at b
        have b' := Order.lt_add_one_iff.1 b
        have c' : c.val ≤ (K c x).val := (hid c).trans (hm2 c zeroValue x (ozl _))
        have heq : psiO fix pow w (ζ + π c) = c.val := le_antisymm b' (c'.trans a)
        have ccrit : Critical (veblenValue fix pow) (baseValue fix pow w) c.val := by
          have hcr := psiO_crit (w := w) h1 h2 ((ltTop c).le.trans hend)
          rw [heq] at hcr
          exact hcr
        have st := crit_step h1 h2 c θc ccrit θcrit hcθ
        rw [hc] at st
        have dbl := (veblen_double h1 h2 c).trans st
        have c1' : c.val ≤ 1 := (add_le_add_iff_left c.val).1 dbl
        have cgt : 1 < c.val := lt_of_lt_of_le (base_gt_one h1 h2) (crit_ge_base h1 h2 ccrit)
        exact absurd c1' (not_le.2 cgt)
      · exact hl
    have Kθ : K θc zeroValue = θc := by
      refine Subtype.ext (le_antisymm ?_ (hid θc))
      refine hlim θc θlim θc.val (fun a haθ => ?_)
      obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
      have o1θ : o1.val < θc.val := by rw [ho1]; exact θgt1
      have o11 : 1 ≤ o1.val := le_of_eq ho1.symm
      rcases le_total a.val o1.val with h | h
      · exact ((hm1 a o1 zeroValue h).trans ((hm2 o1 zeroValue x (ozl _)).trans
          (lowA o1 o11 o1θ))).trans (below o1 o11 o1θ).le
      · have a1 : 1 ≤ a.val := o11.trans h
        exact ((hm2 a zeroValue x (ozl _)).trans (lowA a a1 haθ)).trans (below a a1 haθ).le
    exact (hD x).2.2 θc hxθ Kθ

#print axioms stepBase
#print axioms stepDiagonal

end LogicLineages.PersistentMarking.ActualCalibrationStep
