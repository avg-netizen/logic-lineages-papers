module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepOrbitTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepSuccessorProof

@[expose] public section

/-! The norm of `Ω^ε·c + τ` for an arbitrary exponent `ε` (below `Λ`), `NormPrincipal (Ω^ε)`, the
limit rule for steps, and the steps along a `B_0`-orbit: `(Ω^ε, H)` step ⟹ `(Ω^(ε+e), B_0^e H)`
step for every countable `e`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

/-! Norms at arbitrary exponents. -/

/-- `|Ω^ε·c + τ| = max (max c |ε|) |τ|` for `1 ≤ c < Ω`, `τ < Ω^ε`, the index below `Λ`. -/
theorem norm_leading_gen (ε c τ : Ordinal.{0}) (hc0 : c ≠ 0) (hc : c < omegaIndex)
    (hτ : τ < omegaIndex ^ ε) (hΛ : omegaIndex ^ ε * c + τ < endpoint) :
    coefficientNorm (omegaIndex ^ ε * c + τ) =
      max (max c (coefficientNorm ε)) (coefficientNorm τ) := by
  have hcnf := CNF.opow_mul_add (b := omegaIndex) (e := ε) (x := c) (y := τ) one_lt_index hc0 hc hτ
  have hτΛ : τ < endpoint := lt_of_le_of_lt le_add_self hΛ
  have tail : ((CNF omegaIndex τ).map (fun p => max p.2
      (if h : p.1 < omegaIndex ^ ε * c + τ then coefficientNorm p.1 else 0))).foldr max 0 =
      coefficientNorm τ := by
    rw [norm_eq τ]
    refine congrArg (fun L => List.foldr max 0 L) (List.map_congr_left (fun p hp => ?_))
    have p1 : p.1 < τ := (entry_le hτΛ hp).1
    have p2 : p.1 < omegaIndex ^ ε * c + τ := lt_of_lt_of_le p1 le_add_self
    show max p.2 (if h : p.1 < omegaIndex ^ ε * c + τ then coefficientNorm p.1 else 0) =
      max p.2 (if h : p.1 < τ then coefficientNorm p.1 else 0)
    rw [dif_pos p1, dif_pos p2]
  have cpos : 0 < c := lt_of_le_of_ne (ozl c) (Ne.symm hc0)
  have hpow : omegaIndex ^ ε ≤ omegaIndex ^ ε * c + τ :=
    (Ordinal.le_mul_left (omegaIndex ^ ε) cpos).trans le_self_add
  have hlt : ε < omegaIndex ^ ε * c + τ := by
    by_contra hn
    have a1 : omegaIndex ^ ε * c + τ ≤ ε := not_lt.1 hn
    have a2 : omegaIndex ^ ε ≤ ε := hpow.trans a1
    have a3 : endpoint ≤ omegaIndex ^ ε * c + τ :=
      (exact_EndpointLeast ε a2).trans ((Ordinal.right_le_opow ε one_lt_index).trans hpow)
    exact absurd hΛ (not_lt.2 a3)
  have head : (if h : ε < omegaIndex ^ ε * c + τ then coefficientNorm ε else 0) =
      coefficientNorm ε := dif_pos hlt
  rw [norm_eq (omegaIndex ^ ε * c + τ), hcnf]
  simp only [List.map_cons, List.foldr_cons]
  exact congrArg₂ max (congrArg (max c) head) tail

theorem norm_opow (ε : Ordinal.{0}) (hΛ : omegaIndex ^ ε < endpoint) :
    coefficientNorm (omegaIndex ^ ε) = max 1 (coefficientNorm ε) := by
  have h := norm_leading_gen ε 1 0 one_ne_zero one_lt_index (Ordinal.opow_pos ε omegaIndex_pos)
    (by rw [mul_one, add_zero]; exact hΛ)
  rw [mul_one, add_zero, cnorm_zero, max_eq_left (ozl (max 1 (coefficientNorm ε)))] at h
  exact h

theorem normPrincipal_opow (ε : Ordinal.{0}) (hb : omegaIndex ^ (ε + 1) ≤ endpoint) :
    NormPrincipal (omegaIndex ^ ε) := by
  have hΛε : omegaIndex ^ ε < endpoint :=
    lt_of_lt_of_le ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (Order.lt_add_one_iff.2 le_rfl)) hb
  refine ⟨Ordinal.opow_pos ε omegaIndex_pos, fun c τ hc0 hc hτ => ?_⟩
  have c1 : 1 ≤ c := Order.one_le_iff_ne_zero.2 hc0
  have hΛ : omegaIndex ^ ε * c + τ < endpoint :=
    lt_of_lt_of_le (Ordinal.opow_mul_add_lt_opow hc hτ (Order.lt_add_one_iff.2 le_rfl)) hb
  have e : max c (max 1 (coefficientNorm ε)) = max c (coefficientNorm ε) :=
    le_antisymm
      (max_le (le_max_left _ _) (max_le (c1.trans (le_max_left _ _)) (le_max_right _ _)))
      (max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _)))
  rw [norm_leading_gen ε c τ hc0 hc hτ hΛ, norm_opow ε hΛε, e]

/-- A nonzero index below `Λ` has norm at least 1 and at least the norm of its leading exponent. -/
theorem norm_ge_log (τ : Ordinal.{0}) (hτ0 : τ ≠ 0) (hτ : τ < endpoint) :
    max 1 (coefficientNorm (Ordinal.log omegaIndex τ)) ≤ coefficientNorm τ := by
  have hmem : (Ordinal.log omegaIndex τ, τ / omegaIndex ^ Ordinal.log omegaIndex τ) ∈
      CNF omegaIndex τ := by
    rw [CNF.ne_zero hτ0]
    exact List.mem_cons_self
  obtain ⟨-, a2, a3⟩ := entry_le hτ hmem
  have hpos : 0 < τ / omegaIndex ^ Ordinal.log omegaIndex τ := CNF.snd_pos hmem
  have a1 : (1 : Ordinal.{0}) ≤ τ / omegaIndex ^ Ordinal.log omegaIndex τ := by
    have h := Order.add_one_le_of_lt hpos
    rw [zero_add] at h
    exact h
  exact max_le (a1.trans a2) a3

/-! The limit rule. -/

theorem stepLimit : StepLimit := by
  intro Z s add mul w one pow fix h1 h2 l π πl K Hl hUp hLow hlt hcof hn1 hn2 hstrict hsup hinfl
    hcrit
  have ctx : ∀ (ζ : Ordinal.{0}) (β : CountableOrdinal), β.val < l.val → StepContext ζ πl →
      StepContext ζ (π β) :=
    fun ζ β hβ hc => ⟨le_trans ((add_le_add_iff_left ζ).2 (hlt β hβ).le) hc.1,
      fun τ hτ => hc.2 τ (lt_trans hτ (hlt β hβ))⟩
  refine ⟨?_, ?_⟩
  · intro ζ x hctx hx hψ
    have hend : ζ + πl ≤ endpoint := hctx.1
    have hζend : ζ ≤ endpoint := le_self_add.trans hend
    refine psiO_least h1 h2 hend _ (hcrit x hx) (fun η hη _ => ?_)
    rcases le_total η ζ with h | h
    · exact lt_of_le_of_lt ((psiO_mono h1 h2 hζend h).trans hψ) (hinfl x)
    · have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le h
      have hτ : η - ζ < πl := (Ordinal.sub_lt_of_le h).2 hη
      obtain ⟨β, hβ, hτβ⟩ := hcof (η - ζ) hτ
      have hlt' : η < ζ + π β := lt_of_eq_of_lt hητ.symm ((add_lt_add_iff_left ζ).2 hτβ)
      have hcβ := ctx ζ β hβ hctx
      exact lt_of_le_of_lt
        ((psiO_mono h1 h2 hcβ.1 hlt'.le).trans (hUp β hβ ζ x hcβ hx hψ)) (hstrict β x hβ)
  · intro ζ x hctx hnorm hπθ hx
    have hend : ζ + πl ≤ endpoint := hctx.1
    refine hsup x _ (fun β hβ => ?_)
    have hle : ζ + π β ≤ ζ + πl := (add_le_add_iff_left ζ).2 (hlt β hβ).le
    have hcβ := ctx ζ β hβ hctx
    have act : coefficientNorm ζ < psiO fix pow w (ζ + π β) ∧
        coefficientNorm (π β) < psiO fix pow w (ζ + π β) := by
      by_contra hcon
      have hM : psiO fix pow w (ζ + π β) ≤ max (coefficientNorm ζ) (coefficientNorm (π β)) := by
        rcases not_and_or.1 hcon with h | h
        · exact (not_lt.1 h).trans (le_max_left _ _)
        · exact (not_lt.1 h).trans (le_max_right _ _)
      have hstall : psiO fix pow w (ζ + πl) = psiO fix pow w (ζ + π β) := by
        refine psiO_stall h1 h2 hend hle (fun η hge hlt' => hM.trans ?_)
        have hζη : ζ ≤ η := le_self_add.trans hge
        have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le hζη
        have hτ : η - ζ < πl := (Ordinal.sub_lt_of_le hζη).2 hlt'
        have hle' : π β ≤ η - ζ := (Ordinal.le_sub_of_le hζη).2 hge
        have hs := hctx.2 (η - ζ) hτ
        rw [hητ] at hs
        rw [hs]
        exact max_le_max le_rfl (hn2 β (η - ζ) hβ hle' hτ)
      rw [hstall] at hnorm hπθ
      exact absurd hM (not_le.2 (max_lt hnorm (lt_of_le_of_lt (hn1 β hβ) hπθ)))
    exact (hLow β hβ ζ x hcβ act.1 act.2 hx).trans (psiO_mono h1 h2 hend hle)

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

/-- A fixed point of `a ↦ H^a(0)` above `Γ_0` is critical, for a good `H`. -/
theorem gfix_crit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hG : GoodFn fix pow w H) (κ : CountableOrdinal)
    (hκ : orbit .base H zeroValue κ = κ) (hΓκ : (baseValue fix pow w).val < κ.val) :
    Critical (veblenValue fix pow) (baseValue fix pow w) κ.val := by
  obtain ⟨hH, hN, hC⟩ := hG
  have hpos : 0 < κ.val := lt_of_le_of_lt (ozl _) hΓκ
  have hl := gfix_limit h1 h2 H hH hN κ hκ hpos
  refine critLim h1 h2 κ hpos (fun y hy => ?_)
  have hy' : y.val < (orbit .base H zeroValue κ).val :=
    lt_of_lt_of_eq hy (congrArg Subtype.val hκ).symm
  obtain ⟨a, ha, hya⟩ := lt_orbit_limit H zeroValue κ hl y.val hy'
  refine ⟨orbit .base H (baseValue fix pow w) a,
    orbit_crit h1 h2 H hH hC (baseValue fix pow w) crit_base a, ?_, ?_⟩
  · exact lt_of_lt_of_le hya
      (orbit_start_mono H hH.1 zeroValue (baseValue fix pow w) (ozl _) a)
  · exact (gfix_orbit_closed h1 h2 H hH hN κ hκ hpos (baseValue fix pow w) a hΓκ ha).le

/-- `B_0` maps good functions to good functions, strictly above. -/
theorem good_b0 (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hG : GoodFn fix pow w H) :
    GoodFn fix pow w (towerValue fix 0 H) ∧
    ∀ x : CountableOrdinal, (H x).val < (towerValue fix 0 H x).val := by
  have hH := hG.1
  have hN := hG.2.1
  have T : ∀ x : CountableOrdinal,
      orbit .base H zeroValue (towerValue fix 0 H x) = towerValue fix 0 H x ∧
      x.val < (towerValue fix 0 H x).val := by
    intro x
    have r := fixLeastAbove Z s add mul w one pow fix h1 h2 (fun α => orbit .base H zeroValue α)
      (fun x y hxy => orbit_mono H zeroValue hH.2 hxy)
      (fun x => orbit_id_le H zeroValue hH.2 x)
      (fun l hl => orbit_limit_eq H zeroValue l hl) x
    rw [b0_eq]
    exact ⟨r.1, r.2.1⟩
  obtain ⟨mi, ge⟩ := b0_monoInfl h1 h2 H hH
  refine ⟨⟨mi, fun y => (hN y).trans (ge y), fun x hx => ?_⟩, fun x => ?_⟩
  · exact gfix_crit h1 h2 H hG (towerValue fix 0 H x) (T x).1
      (lt_of_le_of_lt (crit_ge_base h1 h2 hx) (T x).2)
  · exact gfix_closed h1 h2 H hH hN (towerValue fix 0 H x) (T x).1
      (lt_of_le_of_lt (ozl _) (T x).2) x (T x).2

end

theorem stepB0Orbit : StepB0Orbit := by
  intro Z s add mul w one pow fix h1 h2 ε H hbound hsep hstep
  have eqs := orbitEquations (tier 1) (towerValue fix 0) H
  have orbMono := b0Orbit_mono_from h1 h2 H hstep.1.1
  have sepc : ∀ ρ : Ordinal.{0}, ρ < omegaIndex →
      coefficientNorm (ε + ρ) = max (coefficientNorm ε) ρ := by
    intro ρ hρ
    rw [hsep ρ (by rw [Ordinal.opow_one]; exact hρ), norm_countable ρ hρ]
  have bound1 : ∀ ρ : Ordinal.{0}, ρ < omegaIndex → omegaIndex ^ (ε + ρ + 1) ≤ endpoint := by
    intro ρ hρ
    refine le_trans (Ordinal.opow_le_opow_right omegaIndex_pos ?_) hbound
    rw [add_assoc]
    exact (add_le_add_iff_left ε).2 (Order.add_one_le_of_lt hρ)
  have boundlt : ∀ ρ : Ordinal.{0}, ρ < omegaIndex → omegaIndex ^ (ε + ρ) < endpoint :=
    fun ρ hρ => lt_of_lt_of_le
      ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (Order.lt_add_one_iff.2 le_rfl)) (bound1 ρ hρ)
  have normpow : ∀ ρ : Ordinal.{0}, ρ < omegaIndex →
      coefficientNorm (omegaIndex ^ (ε + ρ)) = max 1 (max (coefficientNorm ε) ρ) := by
    intro ρ hρ
    rw [norm_opow (ε + ρ) (boundlt ρ hρ), sepc ρ hρ]
  refine countable_induction _ ?_ ?_ ?_
  · intro e h0
    rw [eqs.1 e h0, h0, add_zero]
    exact hstep
  · intro e' e he ih
    have he'Ω : e'.val < omegaIndex := countable_val_lt e'
    have hP := normPrincipal_opow (ε + e'.val) (bound1 e'.val he'Ω)
    have e1 : omegaIndex ^ (ε + e'.val) * omegaIndex = omegaIndex ^ (ε + e.val) := by
      rw [← Ordinal.opow_add_one, he, add_assoc]
    have hnΩ : coefficientNorm (omegaIndex ^ (ε + e'.val)) ≤
        coefficientNorm (omegaIndex ^ (ε + e'.val) * omegaIndex) := by
      rw [e1, normpow e'.val he'Ω, normpow e.val (countable_val_lt e), he]
      exact max_le_max le_rfl (max_le_max le_rfl le_self_add)
    have st := stepSuccessor Z s add mul w one pow fix h1 h2 (omegaIndex ^ (ε + e'.val))
      (orbit (tier 1) (towerValue fix 0) H e') hP hnΩ ih.1.1 ih.1.2.1 ih.1.2.2 ih.2.1 ih.2.2
    rw [e1] at st
    rw [eqs.2.1 e' e he]
    exact ⟨(good_b0 h1 h2 (orbit (tier 1) (towerValue fix 0) H e') ih.1).1, st.1, st.2⟩
  · intro l hl ih
    have hlΩ : l.val < omegaIndex := countable_val_lt l
    have sup : ∀ x : CountableOrdinal, (orbit (tier 1) (towerValue fix 0) H l x).val =
        ⨆ e : EarlierStages l, (orbit (tier 1) (towerValue fix 0) H (earlierStage l e) x).val :=
      fun x => eqs.2.2 l hl x
    have bdd : ∀ x : CountableOrdinal, BddAbove (Set.range (fun e : EarlierStages l =>
        (orbit (tier 1) (towerValue fix 0) H (earlierStage l e) x).val)) := fun x =>
      bddAbove_orbit .base id
        (fun e : EarlierStages l => orbit (tier 1) (towerValue fix 0) H (earlierStage l e) x)
    have hml : MonoInfl (orbit (tier 1) (towerValue fix 0) H l) := (orbMono l).1
    have stageLe : ∀ β : CountableOrdinal, β.val < l.val → ∀ x : CountableOrdinal,
        (orbit (tier 1) (towerValue fix 0) H β x).val ≤
          (orbit (tier 1) (towerValue fix 0) H l x).val :=
      fun β hβ x => (orbMono l).2 β hβ.le x
    have strict : ∀ β x : CountableOrdinal, β.val < l.val →
        (orbit (tier 1) (towerValue fix 0) H β x).val <
          (orbit (tier 1) (towerValue fix 0) H l x).val := by
      intro β x hβ
      obtain ⟨β1, hβ1⟩ := countable_mk (β.val + 1)
        ((isSuccLimit_omega 1).add_one_lt (countable_val_lt β))
      have hβ1l : β1.val < l.val := by rw [hβ1]; exact hl.add_one_lt hβ
      have a := (good_b0 h1 h2 (orbit (tier 1) (towerValue fix 0) H β) (ih β hβ).1).2 x
      rw [← eqs.2.1 β β1 hβ1] at a
      exact lt_of_lt_of_le a (stageLe β1 hβ1l x)
    have critl : ∀ x : CountableOrdinal,
        Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
        Critical (veblenValue fix pow) (baseValue fix pow w)
          (orbit (tier 1) (towerValue fix 0) H l x).val := by
      intro x hx
      haveI : Nonempty (EarlierStages l) := ⟨⟨0, hl.bot_lt⟩⟩
      refine critLim h1 h2 (orbit (tier 1) (towerValue fix 0) H l x)
        (lt_of_le_of_lt (ozl _) (hml.2 x)) (fun y hy => ?_)
      have hy' := hy
      rw [sup x] at hy'
      obtain ⟨e, he⟩ := (lt_ciSup_iff (bdd x)).1 hy'
      exact ⟨orbit (tier 1) (towerValue fix 0) H (earlierStage l e) x,
        (ih (earlierStage l e) e.property).1.2.2 x hx, he,
        stageLe (earlierStage l e) e.property x⟩
    have geN : ∀ y : CountableOrdinal,
        (veblenValue fix pow y).val ≤ (orbit (tier 1) (towerValue fix 0) H l y).val := by
      intro y
      have h := (orbMono l).2 zeroValue (ozl _) y
      rw [eqs.1 zeroValue rfl] at h
      exact (hstep.1.2.1 y).trans h
    have hsupl : ∀ (x : CountableOrdinal) (b : Ordinal.{0}),
        (∀ β : CountableOrdinal, β.val < l.val →
          (orbit (tier 1) (towerValue fix 0) H β x).val ≤ b) →
        (orbit (tier 1) (towerValue fix 0) H l x).val ≤ b := by
      intro x b Hb
      rw [sup x]
      exact ciSup_le' (fun e => Hb (earlierStage l e) e.property)
    have hcofl : ∀ τ : Ordinal.{0}, τ < omegaIndex ^ (ε + l.val) →
        ∃ β : CountableOrdinal, β.val < l.val ∧ τ < omegaIndex ^ (ε + β.val) := by
      intro τ hτ
      obtain ⟨c', hc', hτc⟩ :=
        (Ordinal.lt_opow_of_isSuccLimit omegaIndex_ne (Ordinal.isSuccLimit_add ε hl)).1 hτ
      obtain ⟨d, hd, hcd⟩ := (Ordinal.lt_add_iff hl.ne_bot).1 hc'
      obtain ⟨β, hβ⟩ := countable_mk d (hd.trans hlΩ)
      refine ⟨β, by rw [hβ]; exact hd, ?_⟩
      rw [hβ]
      exact lt_of_lt_of_le hτc (Ordinal.opow_le_opow_right omegaIndex_pos hcd)
    have hn1l : ∀ β : CountableOrdinal, β.val < l.val →
        coefficientNorm (omegaIndex ^ (ε + β.val)) ≤ coefficientNorm (omegaIndex ^ (ε + l.val)) := by
      intro β hβ
      rw [normpow β.val (countable_val_lt β), normpow l.val hlΩ]
      exact max_le_max le_rfl (max_le_max le_rfl hβ.le)
    have hn2l : ∀ (β : CountableOrdinal) (τ : Ordinal.{0}), β.val < l.val →
        omegaIndex ^ (ε + β.val) ≤ τ → τ < omegaIndex ^ (ε + l.val) →
        coefficientNorm (omegaIndex ^ (ε + β.val)) ≤ coefficientNorm τ := by
      intro β τ hβ hle hτ
      have hτ0 : τ ≠ 0 := by
        intro h0
        rw [h0] at hle
        exact absurd hle (not_le.2 (Ordinal.opow_pos (ε + β.val) omegaIndex_pos))
      have hτΛ : τ < endpoint := lt_trans hτ (boundlt l.val hlΩ)
      have hlog1 : ε + β.val ≤ Ordinal.log omegaIndex τ :=
        Ordinal.le_log_of_opow_le one_lt_index hle
      have hlog2 : Ordinal.log omegaIndex τ < ε + l.val :=
        (Ordinal.lt_opow_iff_log_lt one_lt_index hτ0).1 hτ
      have hεlog : ε ≤ Ordinal.log omegaIndex τ := le_self_add.trans hlog1
      have hρ : Ordinal.log omegaIndex τ - ε < l.val := (Ordinal.sub_lt_of_le hεlog).2 hlog2
      have hρβ : β.val ≤ Ordinal.log omegaIndex τ - ε := (Ordinal.le_sub_of_le hεlog).2 hlog1
      have hnl : coefficientNorm (Ordinal.log omegaIndex τ) =
          max (coefficientNorm ε) (Ordinal.log omegaIndex τ - ε) := by
        have h := sepc (Ordinal.log omegaIndex τ - ε) (hρ.trans hlΩ)
        rw [Ordinal.add_sub_cancel_of_le hεlog] at h
        exact h
      rw [normpow β.val (countable_val_lt β)]
      refine le_trans ?_ (norm_ge_log τ hτ0 hτΛ)
      rw [hnl]
      exact max_le_max le_rfl (max_le_max le_rfl hρβ)
    have st := stepLimit Z s add mul w one pow fix h1 h2 l (fun β => omegaIndex ^ (ε + β.val))
      (omegaIndex ^ (ε + l.val)) (fun β => orbit (tier 1) (towerValue fix 0) H β)
      (orbit (tier 1) (towerValue fix 0) H l)
      (fun β hβ => (ih β hβ).2.1) (fun β hβ => (ih β hβ).2.2)
      (fun β hβ => (Ordinal.opow_lt_opow_iff_right one_lt_index).2 ((add_lt_add_iff_left ε).2 hβ))
      hcofl hn1l hn2l strict hsupl (fun x => hml.2 x) critl
    exact ⟨⟨hml, geN, critl⟩, st.1, st.2⟩

#print axioms norm_leading_gen
#print axioms stepLimit
#print axioms stepB0Orbit

end LogicLineages.PersistentMarking.ActualCalibrationStep
