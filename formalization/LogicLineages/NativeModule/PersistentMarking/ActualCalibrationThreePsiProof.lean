module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeCriticalProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeNormProof

@[expose] public section

/-! ψ side of n = 3: generic facts about the (P)-collapse (monotone, stall), and the two
induction-loading inequalities `UpperStep`, `LowerStep`, each by induction on the exponent. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

theorem psiO_eq {ξ : Ordinal.{0}} (hξ : ξ ≤ endpoint) :
    psiO fix pow w ξ = (veblenData fix pow w).psi ⟨ξ, hξ⟩ := by
  unfold psiO
  rw [dif_pos hξ]

theorem psi_char (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    CharacterizationP (actualData (veblenValue fix pow) (baseValue fix pow w)) :=
  actualCharacterization (veblenValue fix pow) (baseValue fix pow w)
    (veblenInflationary Z s add mul w one pow fix h1 h2).1
    (veblenInflationary Z s add mul w one pow fix h1 h2).2

theorem psiO_crit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) {ξ : Ordinal.{0}} (hξ : ξ ≤ endpoint) :
    Critical (veblenValue fix pow) (baseValue fix pow w) (psiO fix pow w ξ) := by
  rw [psiO_eq hξ]
  exact (psi_char h1 h2 ⟨ξ, hξ⟩).1

theorem psiO_closure (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) {ξ η : Ordinal.{0}} (hξ : ξ ≤ endpoint)
    (hη : η < ξ) (hn : coefficientNorm η < psiO fix pow w ξ) :
    psiO fix pow w η < psiO fix pow w ξ := by
  rw [psiO_eq hξ] at hn ⊢
  rw [psiO_eq (hη.le.trans hξ)]
  exact (psi_char h1 h2 ⟨ξ, hξ⟩).2.1 ⟨η, hη.le.trans hξ⟩ hη hn

theorem psiO_least (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) {ξ : Ordinal.{0}} (hξ : ξ ≤ endpoint)
    (θ : Ordinal.{0}) (hθ : Critical (veblenValue fix pow) (baseValue fix pow w) θ)
    (H : ∀ η : Ordinal.{0}, η < ξ → coefficientNorm η < θ → psiO fix pow w η < θ) :
    psiO fix pow w ξ ≤ θ := by
  rw [psiO_eq hξ]
  refine (psi_char h1 h2 ⟨ξ, hξ⟩).2.2 θ hθ (fun η' hη' hn => ?_)
  have h := H η'.val hη' hn
  rw [psiO_eq η'.property] at h
  exact h

/-- The (P)-collapse is weakly monotone. -/
theorem psiO_mono (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) {ξ ξ' : Ordinal.{0}} (hξ' : ξ' ≤ endpoint)
    (h : ξ ≤ ξ') : psiO fix pow w ξ ≤ psiO fix pow w ξ' :=
  psiO_least h1 h2 (h.trans hξ') (psiO fix pow w ξ') (psiO_crit h1 h2 hξ')
    (fun _ hη hn => psiO_closure h1 h2 hξ' (lt_of_lt_of_le hη h) hn)

/-- Stall: if every index in `[ζ, ξ)` has norm at least `ψ ζ`, then `ψ ξ = ψ ζ`. -/
theorem psiO_stall (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) {ζ ξ : Ordinal.{0}} (hξ : ξ ≤ endpoint)
    (h : ζ ≤ ξ)
    (H : ∀ η : Ordinal.{0}, ζ ≤ η → η < ξ → psiO fix pow w ζ ≤ coefficientNorm η) :
    psiO fix pow w ξ = psiO fix pow w ζ := by
  refine le_antisymm (psiO_least h1 h2 hξ (psiO fix pow w ζ) (psiO_crit h1 h2 (h.trans hξ))
    (fun η hη hn => ?_)) (psiO_mono h1 h2 hξ h)
  rcases lt_or_ge η ζ with hlt | hge
  · exact psiO_closure h1 h2 (h.trans hξ) hlt hn
  · exact absurd (H η hge hη) (not_le.2 hn)

theorem psiO_gt_one (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) {ξ : Ordinal.{0}} (hξ : ξ ≤ endpoint) :
    1 < psiO fix pow w ξ :=
  lt_of_lt_of_le (base_gt_one h1 h2) (crit_ge_base h1 h2 (psiO_crit h1 h2 hξ))

theorem psiO_zero_le (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    psiO fix pow w 0 ≤ (baseValue fix pow w).val :=
  psiO_least h1 h2 (ozl endpoint) (baseValue fix pow w).val crit_base
    (fun _ hη _ => absurd hη not_lt_zero)

end

theorem upperStep : UpperStep := by
  intro Z s add mul w one pow fix h1 h2
  have infl := veblen_infl h1 h2
  refine countable_induction _ ?_ ?_ ?_
  · -- e = 0
    intro e h0 ζ x hTop _ hx hψ
    have hend : ζ + omegaIndex ^ e.val ≤ endpoint := hTop.trans top_le_endpoint
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    have eN : level fix pow e x = veblenValue fix pow x := congrFun (level_zero_eq e h0) x
    rw [eN]
    refine psiO_least h1 h2 hend _ (crit_succ x hx) (fun η hη _ => ?_)
    have hη' : η ≤ ζ := by
      rw [h0, Ordinal.opow_zero] at hη
      exact Order.lt_add_one_iff.1 hη
    exact lt_of_le_of_lt ((psiO_mono h1 h2 hζend hη').trans hψ) (infl x)
  · -- e = e' + 1
    intro e' e he ih ζ x hTop hSep hx hψ
    have hm := level_monoInfl h1 h2 e'
    have he' : e'.val < omegaIndex := countable_val_lt e'
    rw [he] at hTop hSep ⊢
    have hend : ζ + omegaIndex ^ (e'.val + 1) ≤ endpoint := hTop.trans top_le_endpoint
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    obtain ⟨hfix, hxκ, -⟩ := level_step h1 h2 e' e he x
    have hpos : 0 < (level fix pow e x).val := lt_of_le_of_lt (ozl _) hxκ
    have hlim := enumFix_limit h1 h2 e' (level fix pow e x) hfix hpos
    have κcrit := level_critical h1 h2 e (by rw [he]; exact le_add_self) x
    have bnd : ∀ b : CountableOrdinal,
        ζ + omegaIndex ^ e'.val * b.val ≤ omegaIndex ^ omegaIndex := by
      intro b
      refine le_trans ((add_le_add_iff_left ζ).2 ?_) hTop
      rw [Ordinal.opow_add_one]
      exact mul_le_mul' le_rfl (countable_val_lt b).le
    have chain : ∀ b : CountableOrdinal,
        Critical (veblenValue fix pow) (baseValue fix pow w)
          (orbit .base (level fix pow e') x b).val ∧
        psiO fix pow w (ζ + omegaIndex ^ e'.val * b.val) ≤
          (orbit .base (level fix pow e') x b).val := by
      refine countable_induction _ ?_ ?_ ?_
      · intro b h0
        rw [orbit_zero (level fix pow e') x b h0, h0, mul_zero, add_zero]
        exact ⟨hx, hψ⟩
      · intro b' b hb ihb
        have e1 : ζ + omegaIndex ^ e'.val * b'.val + omegaIndex ^ e'.val =
            ζ + omegaIndex ^ e'.val * b.val := by
          rw [hb, mul_add_one, add_assoc]
        have key := ih (ζ + omegaIndex ^ e'.val * b'.val) (orbit .base (level fix pow e') x b')
        rw [e1] at key
        rw [orbit_succ (level fix pow e') x b' b hb]
        refine ⟨?_, key (bnd b) (nsep_step hSep he' (countable_val_lt b')) ihb.1 ihb.2⟩
        by_cases e0 : e'.val = 0
        · have eN : level fix pow e' (orbit .base (level fix pow e') x b') =
              veblenValue fix pow (orbit .base (level fix pow e') x b') :=
            congrFun (level_zero_eq e' e0) _
          rw [eN]
          exact crit_succ _ ihb.1
        · exact level_critical h1 h2 e' (Order.one_le_iff_ne_zero.2 e0) _
      · intro l hl ihl
        have hposl : 0 < (orbit .base (level fix pow e') x l).val :=
          lt_of_lt_of_le hl.bot_lt (orbit_id_le (level fix pow e') x hm.2 l)
        have crit : Critical (veblenValue fix pow) (baseValue fix pow w)
            (orbit .base (level fix pow e') x l).val := by
          refine critLim h1 h2 (orbit .base (level fix pow e') x l) hposl (fun y hy => ?_)
          obtain ⟨β, hβ, hyβ⟩ := lt_orbit_limit (level fix pow e') x l hl y.val hy
          exact ⟨orbit .base (level fix pow e') x β, (ihl β hβ).1, hyβ,
            orbit_le_limit (level fix pow e') x l hl β hβ⟩
        refine ⟨crit, psiO_least h1 h2 ((bnd l).trans top_le_endpoint) _ crit (fun η hη _ => ?_)⟩
        obtain ⟨b', hb', hlt⟩ : ∃ b' : CountableOrdinal, b'.val < l.val ∧
            η < ζ + omegaIndex ^ e'.val * b'.val := by
          rcases lt_or_ge η ζ with h | h
          · exact ⟨zeroValue, hl.bot_lt, lt_of_lt_of_le h le_self_add⟩
          · have hsub : η - ζ < omegaIndex ^ e'.val * l.val := (Ordinal.sub_lt_of_le h).2 hη
            obtain ⟨c', hc'l, hc'⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit hl).1 hsub
            obtain ⟨b', hb'⟩ := countable_mk c' (hc'l.trans (countable_val_lt l))
            refine ⟨b', by rw [hb']; exact hc'l, ?_⟩
            rw [hb']
            exact lt_of_eq_of_lt (Ordinal.add_sub_cancel_of_le h).symm
              ((add_lt_add_iff_left ζ).2 hc')
        exact lt_of_le_of_lt
          ((psiO_mono h1 h2 ((bnd b').trans top_le_endpoint) hlt.le).trans (ihl b' hb').2)
          (orbit_strictMono (level fix pow e') x hm.2 b' l hb')
    refine psiO_least h1 h2 hend _ κcrit (fun η hη hn => ?_)
    rcases le_total η ζ with h | h
    · exact lt_of_le_of_lt ((psiO_mono h1 h2 hζend h).trans hψ) hxκ
    · have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le h
      have hτ : η - ζ < omegaIndex ^ (e'.val + 1) := (Ordinal.sub_lt_of_le h).2 hη
      have hnorm : coefficientNorm (η - ζ) ≤ coefficientNorm η := by
        have hs := hSep (η - ζ) hτ
        rw [hητ] at hs
        rw [hs]
        exact le_max_right _ _
      obtain ⟨b, hbΩ, hbn, hτb⟩ := norm_div_le e'.val (η - ζ) he' hτ
      obtain ⟨b1, hb1⟩ := countable_mk (b + 1) ((isSuccLimit_omega 1).add_one_lt hbΩ)
      have hb1κ : b1.val < (level fix pow e x).val := by
        rw [hb1]
        exact hlim.add_one_lt (lt_of_le_of_lt (hbn.trans hnorm) hn)
      have hlt : η < ζ + omegaIndex ^ e'.val * b1.val := by
        rw [hb1]
        exact lt_of_eq_of_lt hητ.symm ((add_lt_add_iff_left ζ).2 hτb)
      exact lt_of_le_of_lt
        ((psiO_mono h1 h2 ((bnd b1).trans top_le_endpoint) hlt.le).trans (chain b1).2)
        (enumFix_orbit_closed h1 h2 e' (level fix pow e x) hfix hpos x b1 hxκ hb1κ)
  · -- e limit
    intro l hl ih ζ x hTop hSep hx hψ
    have hend : ζ + omegaIndex ^ l.val ≤ endpoint := hTop.trans top_le_endpoint
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    have hml := level_monoInfl h1 h2 l
    have κcrit := level_critical h1 h2 l (Ordinal.one_lt_of_isSuccLimit hl).le x
    refine psiO_least h1 h2 hend _ κcrit (fun η hη _ => ?_)
    rcases le_total η ζ with h | h
    · exact lt_of_le_of_lt ((psiO_mono h1 h2 hζend h).trans hψ) (hml.2 x)
    · have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le h
      have hτ : η - ζ < omegaIndex ^ l.val := (Ordinal.sub_lt_of_le h).2 hη
      obtain ⟨c', hc'l, hc'⟩ := (Ordinal.lt_opow_of_isSuccLimit omegaIndex_ne hl).1 hτ
      obtain ⟨β, hβ⟩ := countable_mk c' (hc'l.trans (countable_val_lt l))
      obtain ⟨β1, hβ1⟩ := countable_mk (β.val + 1)
        ((isSuccLimit_omega 1).add_one_lt (countable_val_lt β))
      have hβl : β.val < l.val := by rw [hβ]; exact hc'l
      have hβ1l : β1.val < l.val := by rw [hβ1]; exact hl.add_one_lt hβl
      have hpowle : omegaIndex ^ β.val ≤ omegaIndex ^ l.val :=
        Ordinal.opow_le_opow_right omegaIndex_pos hβl.le
      have hTopβ : ζ + omegaIndex ^ β.val ≤ omegaIndex ^ omegaIndex :=
        le_trans ((add_le_add_iff_left ζ).2 hpowle) hTop
      have hlt : η < ζ + omegaIndex ^ β.val := by
        rw [hβ]
        exact lt_of_eq_of_lt hητ.symm ((add_lt_add_iff_left ζ).2 hc')
      have a := ih β hβl ζ x hTopβ (nsep_mono hSep hβl.le) hx hψ
      exact lt_of_le_of_lt ((psiO_mono h1 h2 (hTopβ.trans top_le_endpoint) hlt.le).trans a)
        (lt_of_lt_of_le (level_lt_succ h1 h2 β β1 hβ1 x) (level_mono_index h1 h2 β1 l hβ1l.le x))

theorem lowerStep : LowerStep := by
  intro Z s add mul w one pow fix h1 h2
  refine countable_induction _ ?_ ?_ ?_
  · -- e = 0
    intro e h0 ζ x hTop _ hnorm _ hx
    have hend : ζ + omegaIndex ^ e.val ≤ endpoint := hTop.trans top_le_endpoint
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    have hζlt : ζ < ζ + omegaIndex ^ e.val := by
      have h := (add_lt_add_iff_left ζ).2 (Ordinal.opow_pos e.val omegaIndex_pos)
      rw [add_zero] at h
      exact h
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
    have eN : level fix pow e x = veblenValue fix pow x := congrFun (level_zero_eq e h0) x
    rw [eN, ← hθc]
    exact le_trans ((veblen_monoInfl h1 h2).1 x pc (by rw [hpc]; exact hx)) st
  · -- e = e' + 1
    intro e' e he ih ζ x hTop hSep hnorm heθ hx
    have hm := level_monoInfl h1 h2 e'
    have he' : e'.val < omegaIndex := countable_val_lt e'
    rw [he] at hTop hSep hnorm heθ ⊢
    have hend : ζ + omegaIndex ^ (e'.val + 1) ≤ endpoint := hTop.trans top_le_endpoint
    obtain ⟨θc, hθc⟩ := crit_val (psiO_crit (w := w) h1 h2 hend)
    rw [← hθc] at hnorm heθ ⊢
    have θcrit : Critical (veblenValue fix pow) (baseValue fix pow w) θc.val := by
      rw [hθc]
      exact psiO_crit h1 h2 hend
    have θgt1 : 1 < θc.val := by
      rw [hθc]
      exact psiO_gt_one h1 h2 hend
    have e'θ : e'.val < θc.val := lt_trans (Order.lt_add_one_iff.2 le_rfl) heθ
    have bnd : ∀ b : CountableOrdinal,
        ζ + omegaIndex ^ e'.val * b.val ≤ omegaIndex ^ omegaIndex := by
      intro b
      refine le_trans ((add_le_add_iff_left ζ).2 ?_) hTop
      rw [Ordinal.opow_add_one]
      exact mul_le_mul' le_rfl (countable_val_lt b).le
    have bndE : ∀ b : CountableOrdinal, ζ + omegaIndex ^ e'.val * b.val ≤ endpoint :=
      fun b => (bnd b).trans top_le_endpoint
    have ltTop : ∀ b : CountableOrdinal,
        ζ + omegaIndex ^ e'.val * b.val < ζ + omegaIndex ^ (e'.val + 1) := by
      intro b
      refine (add_lt_add_iff_left ζ).2 ?_
      rw [Ordinal.opow_add_one]
      exact mul_lt_mul_of_pos_left (countable_val_lt b) (Ordinal.opow_pos e'.val omegaIndex_pos)
    have closure : ∀ η : Ordinal.{0}, η < ζ + omegaIndex ^ (e'.val + 1) →
        coefficientNorm η < θc.val → psiO fix pow w η < θc.val := by
      intro η hη hn
      rw [hθc] at hn ⊢
      exact psiO_closure h1 h2 hend hη hn
    have normξ_le : ∀ b : CountableOrdinal,
        coefficientNorm (ζ + omegaIndex ^ e'.val * b.val) ≤
          max (coefficientNorm ζ) (max b.val e'.val) := by
      intro b
      by_cases hb0 : b.val = 0
      · rw [hb0, mul_zero, add_zero]
        exact le_max_left _ _
      · exact le_of_eq (nsep_norm_mul hSep he' hb0 (countable_val_lt b))
    have below : ∀ b : CountableOrdinal, b.val < θc.val →
        psiO fix pow w (ζ + omegaIndex ^ e'.val * b.val) < θc.val :=
      fun b hb => closure _ (ltTop b)
        (lt_of_le_of_lt (normξ_le b) (max_lt hnorm (max_lt hb e'θ)))
    have active : ∀ b' b : CountableOrdinal, b.val = b'.val + 1 → b.val < θc.val →
        coefficientNorm (ζ + omegaIndex ^ e'.val * b'.val) <
          psiO fix pow w (ζ + omegaIndex ^ e'.val * b.val) ∧
        e'.val < psiO fix pow w (ζ + omegaIndex ^ e'.val * b.val) := by
      intro b' b hb hbθ
      by_contra hcon
      have hb'b : b'.val ≤ b.val := by rw [hb]; exact le_self_add
      have hM : psiO fix pow w (ζ + omegaIndex ^ e'.val * b.val) ≤
          max (coefficientNorm ζ) (max b.val e'.val) := by
        rcases not_and_or.1 hcon with h | h
        · exact (not_lt.1 h).trans ((normξ_le b').trans
            (max_le_max le_rfl (max_le_max hb'b le_rfl)))
        · exact (not_lt.1 h).trans ((le_max_right _ _).trans (le_max_right _ _))
      have hb1 : 1 ≤ b.val := by rw [hb]; exact le_add_self
      have hstall : psiO fix pow w (ζ + omegaIndex ^ (e'.val + 1)) =
          psiO fix pow w (ζ + omegaIndex ^ e'.val * b.val) := by
        refine psiO_stall h1 h2 hend (ltTop b).le (fun η hge hlt => hM.trans ?_)
        have hζη : ζ ≤ η := le_self_add.trans hge
        have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le hζη
        have hτ : η - ζ < omegaIndex ^ (e'.val + 1) := (Ordinal.sub_lt_of_le hζη).2 hlt
        have hle : omegaIndex ^ e'.val * b.val ≤ η - ζ := (Ordinal.le_sub_of_le hζη).2 hge
        have nf := norm_ge_of_mul_le e'.val b.val (η - ζ) he' hb1 hle hτ
        have hs := hSep (η - ζ) hτ
        rw [hητ] at hs
        rw [hs]
        exact max_le_max le_rfl nf
      have hθM : θc.val ≤ max (coefficientNorm ζ) (max b.val e'.val) := by
        rw [hθc, hstall]
        exact hM
      exact absurd hθM (not_le.2 (max_lt hnorm (max_lt hbθ e'θ)))
    have chain : ∀ b : CountableOrdinal, b.val < θc.val →
        (orbit .base (level fix pow e') x b).val ≤
          psiO fix pow w (ζ + omegaIndex ^ e'.val * b.val) := by
      refine countable_induction _ ?_ ?_ ?_
      · intro b h0 _
        rw [orbit_zero (level fix pow e') x b h0, h0, mul_zero, add_zero]
        exact hx
      · intro b' b hb ihb hbθ
        have hb'b : b'.val ≤ b.val := by rw [hb]; exact le_self_add
        have hb'θ : b'.val < θc.val := lt_of_le_of_lt hb'b hbθ
        have e1 : ζ + omegaIndex ^ e'.val * b'.val + omegaIndex ^ e'.val =
            ζ + omegaIndex ^ e'.val * b.val := by
          rw [hb, mul_add_one, add_assoc]
        have key := ih (ζ + omegaIndex ^ e'.val * b'.val) (orbit .base (level fix pow e') x b')
        rw [e1] at key
        rw [orbit_succ (level fix pow e') x b' b hb]
        obtain ⟨a1, a2⟩ := active b' b hb hbθ
        exact key (bnd b) (nsep_step hSep he' (countable_val_lt b')) a1 a2 (ihb hb'θ)
      · intro l hl ihl hlθ
        refine orbit_limit_le (level fix pow e') x l hl _ (fun β hβ => ?_)
        exact (ihl β hβ (lt_trans hβ hlθ)).trans (psiO_mono h1 h2 (bndE l)
          ((add_le_add_iff_left ζ).2 (mul_le_mul' le_rfl hβ.le)))
    have hζlt : ζ < ζ + omegaIndex ^ (e'.val + 1) := by
      have h := (add_lt_add_iff_left ζ).2 (Ordinal.opow_pos (e'.val + 1) omegaIndex_pos)
      rw [add_zero] at h
      exact h
    have hxθ : x.val < θc.val := lt_of_le_of_lt hx (closure ζ hζlt hnorm)
    have θlim : Order.IsSuccLimit θc.val := by
      rcases countable_cases θc with h0 | ⟨c, hc⟩ | hl
      · exact absurd θgt1 (by rw [h0]; exact not_lt.2 zero_le_one)
      · exfalso
        have hcθ : c.val < θc.val := by rw [hc]; exact Order.lt_add_one_iff.2 le_rfl
        have a := chain c hcθ
        have b := below c hcθ
        rw [hc] at b
        have b' := Order.lt_add_one_iff.1 b
        have c' : c.val ≤ (orbit .base (level fix pow e') x c).val :=
          orbit_id_le (level fix pow e') x hm.2 c
        have heq : psiO fix pow w (ζ + omegaIndex ^ e'.val * c.val) = c.val :=
          le_antisymm b' (c'.trans a)
        have ccrit : Critical (veblenValue fix pow) (baseValue fix pow w) c.val := by
          have hcr := psiO_crit (w := w) h1 h2 (bndE c)
          rw [heq] at hcr
          exact hcr
        have st := crit_step h1 h2 c θc ccrit θcrit hcθ
        rw [hc] at st
        have dbl := (veblen_double h1 h2 c).trans st
        have c1 : c.val ≤ 1 := (add_le_add_iff_left c.val).1 dbl
        have cgt : 1 < c.val := lt_of_lt_of_le (base_gt_one h1 h2) (crit_ge_base h1 h2 ccrit)
        exact absurd c1 (not_le.2 cgt)
      · exact hl
    have Eθ : levelEnum fix pow e' θc = θc := by
      refine Subtype.ext (le_antisymm ?_ (lvEnum_id_le h1 h2 e' θc))
      refine orbit_limit_le (level fix pow e') zeroValue θc θlim _ (fun b hb => ?_)
      exact ((orbit_start_mono (level fix pow e') hm.1 zeroValue x (ozl _) b).trans
        (chain b hb)).trans (below b hb).le
    exact (level_step h1 h2 e' e he x).2.2 θc hxθ Eθ
  · -- e limit
    intro l hl ih ζ x hTop hSep hnorm hlθ hx
    have hend : ζ + omegaIndex ^ l.val ≤ endpoint := hTop.trans top_le_endpoint
    refine level_limit_le l hl x _ (fun β hβ => ?_)
    have hpow : omegaIndex ^ β.val ≤ omegaIndex ^ l.val :=
      Ordinal.opow_le_opow_right omegaIndex_pos hβ.le
    have hle : ζ + omegaIndex ^ β.val ≤ ζ + omegaIndex ^ l.val := (add_le_add_iff_left ζ).2 hpow
    have hTopβ : ζ + omegaIndex ^ β.val ≤ omegaIndex ^ omegaIndex := hle.trans hTop
    have act : coefficientNorm ζ < psiO fix pow w (ζ + omegaIndex ^ β.val) ∧
        β.val < psiO fix pow w (ζ + omegaIndex ^ β.val) := by
      by_contra hcon
      have hM : psiO fix pow w (ζ + omegaIndex ^ β.val) ≤ max (coefficientNorm ζ) β.val := by
        rcases not_and_or.1 hcon with h | h
        · exact (not_lt.1 h).trans (le_max_left _ _)
        · exact (not_lt.1 h).trans (le_max_right _ _)
      have hstall : psiO fix pow w (ζ + omegaIndex ^ l.val) =
          psiO fix pow w (ζ + omegaIndex ^ β.val) := by
        refine psiO_stall h1 h2 hend hle (fun η hge hlt => hM.trans ?_)
        have hζη : ζ ≤ η := le_self_add.trans hge
        have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le hζη
        have hτ : η - ζ < omegaIndex ^ l.val := (Ordinal.sub_lt_of_le hζη).2 hlt
        have hle' : omegaIndex ^ β.val ≤ η - ζ := (Ordinal.le_sub_of_le hζη).2 hge
        have nf := norm_ge_exponent β.val l.val (η - ζ) (countable_val_lt l) hle' hτ
        have hs := hSep (η - ζ) hτ
        rw [hητ] at hs
        rw [hs]
        exact max_le_max le_rfl nf
      rw [hstall] at hnorm hlθ
      exact absurd hM (not_le.2 (max_lt hnorm (lt_trans hβ hlθ)))
    exact (ih β hβ ζ x hTopβ (nsep_mono hSep hβ.le) act.1 act.2 hx).trans
      (psiO_mono h1 h2 hend hle)

#print axioms upperStep
#print axioms lowerStep

end LogicLineages.PersistentMarking.ActualCalibrationThree
