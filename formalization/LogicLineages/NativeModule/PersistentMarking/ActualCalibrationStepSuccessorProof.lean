module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepDiagonalProof

@[expose] public section

/-! The successor rule of the step calculus: if `(π, H)` is a step then `(π·Ω, B_0 H)` is a step.
Ingredients: positive fixed points of `a ↦ H^a(0)` for a monotone inflationary `H ≥ N_B` (limit,
closed under `+`, under `H`, under `H`-orbits); the norm calculus of a norm-principal `π`; the
composites `(π·a, H^a)` of one step; and the diagonal lemma. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

/-! Norm-principal increments. -/

theorem np_ne {π : Ordinal.{0}} (hP : NormPrincipal π) : π ≠ 0 :=
  fun h => absurd hP.1 (by rw [h]; exact lt_irrefl _)

theorem np_norm_mul {π c : Ordinal.{0}} (hP : NormPrincipal π) (hc0 : c ≠ 0) (hc : c < omegaIndex) :
    coefficientNorm (π * c) = max c (coefficientNorm π) := by
  have h := hP.2 c 0 hc0 hc hP.1
  rw [add_zero, cnorm_zero, max_eq_left (ozl (max c (coefficientNorm π)))] at h
  exact h

theorem np_div_le {π τ : Ordinal.{0}} (hP : NormPrincipal π) (hτ : τ < π * omegaIndex) :
    ∃ b : Ordinal.{0}, b < omegaIndex ∧ b ≤ coefficientNorm τ ∧ τ < π * (b + 1) := by
  have hne := np_ne hP
  have hb : τ / π < omegaIndex := (Ordinal.div_lt hne).2 hτ
  refine ⟨τ / π, hb, ?_, ?_⟩
  · by_cases hb0 : τ / π = 0
    · rw [hb0]
      exact ozl _
    · have hn := hP.2 (τ / π) (τ % π) hb0 hb (Ordinal.mod_lt τ hne)
      rw [Ordinal.div_add_mod] at hn
      rw [hn]
      exact (le_max_left _ _).trans (le_max_left _ _)
  · have h := Ordinal.lt_mul_succ_div τ hne
    rw [← Ordinal.add_one_eq_succ] at h
    exact h

theorem np_ge {π b τ : Ordinal.{0}} (hP : NormPrincipal π) (hb1 : 1 ≤ b) (hle : π * b ≤ τ)
    (hτ : τ < π * omegaIndex) : max b (coefficientNorm π) ≤ coefficientNorm τ := by
  have hne := np_ne hP
  have hc : τ / π < omegaIndex := (Ordinal.div_lt hne).2 hτ
  have hbc : b ≤ τ / π := (Ordinal.le_div hne).2 hle
  have hc0 : τ / π ≠ 0 := by
    intro h0
    rw [h0] at hbc
    exact absurd (hb1.trans hbc) (not_le.2 zero_lt_one)
  have hn := hP.2 (τ / π) (τ % π) hc0 hc (Ordinal.mod_lt τ hne)
  rw [Ordinal.div_add_mod] at hn
  rw [hn]
  exact max_le ((hbc.trans (le_max_left _ _)).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))

theorem ctx_norm_le {ζ π a c : Ordinal.{0}} (hP : NormPrincipal π) (hctx : StepContext ζ (π * a))
    (hc : c < omegaIndex) (hca : c < a) :
    coefficientNorm (ζ + π * c) ≤ max (coefficientNorm ζ) (max c (coefficientNorm π)) := by
  by_cases hc0 : c = 0
  · rw [hc0, mul_zero, add_zero]
    exact le_max_left _ _
  · have e : coefficientNorm (ζ + π * c) = max (coefficientNorm ζ) (max c (coefficientNorm π)) := by
      rw [hctx.2 (π * c) (mul_lt_mul_of_pos_left hca hP.1), np_norm_mul hP hc0 hc]
    exact le_of_eq e

theorem ctx_step {ζ π a c : Ordinal.{0}} (hP : NormPrincipal π) (hctx : StepContext ζ (π * a))
    (hc : c < omegaIndex) (hca : c + 1 ≤ a) : StepContext (ζ + π * c) π := by
  have hπ1 : π * (c + 1) ≤ π * a := mul_le_mul' le_rfl hca
  refine ⟨?_, fun τ hτ => ?_⟩
  · have e : ζ + π * c + π = ζ + π * (c + 1) := by rw [mul_add_one, add_assoc]
    rw [e]
    exact le_trans ((add_le_add_iff_left ζ).2 hπ1) hctx.1
  · have hlt0 : π * c + τ < π * (c + 1) := by
      rw [mul_add_one]
      exact (add_lt_add_iff_left (π * c)).2 hτ
    have hlt : π * c + τ < π * a := lt_of_lt_of_le hlt0 hπ1
    by_cases hc0 : c = 0
    · rw [hc0, mul_zero, zero_add] at hlt
      rw [hc0, mul_zero, add_zero]
      exact hctx.2 τ hlt
    · have hca' : c < a := lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl) hca
      have e1 : ζ + π * c + τ = ζ + (π * c + τ) := add_assoc _ _ _
      rw [e1, hctx.2 (π * c + τ) hlt, hP.2 c τ hc0 hc hτ,
        hctx.2 (π * c) (mul_lt_mul_of_pos_left hca' hP.1), np_norm_mul hP hc0 hc]
      exact (max_assoc _ _ _).symm

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

/-! Positive fixed points of `a ↦ H^a(0)` for monotone inflationary `H ≥ N_B`. -/

theorem gfix_gt_omega (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hH : MonoInfl H)
    (hN : ∀ y : CountableOrdinal, (veblenValue fix pow y).val ≤ (H y).val) (κ : CountableOrdinal)
    (hκ : orbit .base H zeroValue κ = κ) (hpos : 0 < κ.val) : (ω : Ordinal.{0}) < κ.val := by
  obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
  have e1 : orbit .base H zeroValue o1 = H zeroValue := by
    rw [orbit_succ H zeroValue zeroValue o1 (ho1.trans (zero_add (1 : Ordinal.{0})).symm),
      orbit_zero H zeroValue zeroValue rfl]
  have hω : (ω : Ordinal.{0}) ≤ (H zeroValue).val :=
    (omega_le_veblen h1 h2 zeroValue).trans (hN zeroValue)
  have one_le : o1.val ≤ κ.val := by
    rw [ho1]
    have h := Order.add_one_le_of_lt hpos
    rw [zero_add] at h
    exact h
  have a : (orbit .base H zeroValue o1).val ≤ (orbit .base H zeroValue κ).val :=
    orbit_mono H zeroValue hH.2 one_le
  rw [e1, hκ] at a
  obtain ⟨o2, ho2⟩ := countable_mk (o1.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt o1))
  have two_le : o2.val ≤ κ.val := by
    rw [ho2, ho1]
    exact one_add_one_lt_omega.le.trans (hω.trans a)
  have b : (orbit .base H zeroValue o2).val ≤ (orbit .base H zeroValue κ).val :=
    orbit_mono H zeroValue hH.2 two_le
  rw [orbit_succ H zeroValue o1 o2 ho2, e1, hκ] at b
  exact lt_of_le_of_lt hω (lt_of_lt_of_le (hH.2 (H zeroValue)) b)

theorem gfix_limit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hH : MonoInfl H)
    (hN : ∀ y : CountableOrdinal, (veblenValue fix pow y).val ≤ (H y).val) (κ : CountableOrdinal)
    (hκ : orbit .base H zeroValue κ = κ) (hpos : 0 < κ.val) : Order.IsSuccLimit κ.val := by
  rcases countable_cases κ with h0 | ⟨c, hc⟩ | hl
  · exact absurd hpos (by rw [h0]; exact lt_irrefl _)
  · exfalso
    have big := gfix_gt_omega h1 h2 H hH hN κ hκ hpos
    have a : (orbit .base H zeroValue c).val + (orbit .base H zeroValue c).val ≤
        (H (orbit .base H zeroValue c)).val :=
      (veblen_double h1 h2 (orbit .base H zeroValue c)).trans (hN (orbit .base H zeroValue c))
    rw [← orbit_succ H zeroValue c κ hc, hκ] at a
    have b : c.val + c.val ≤ c.val + 1 := by
      rw [← hc]
      exact (add_le_add (orbit_id_le H zeroValue hH.2 c) (orbit_id_le H zeroValue hH.2 c)).trans a
    have c1 : c.val ≤ 1 := (add_le_add_iff_left c.val).1 b
    have small : κ.val ≤ 1 + 1 := by
      rw [hc]
      exact add_le_add c1 le_rfl
    exact absurd (lt_of_lt_of_le big small) (not_lt.2 one_add_one_lt_omega.le)
  · exact hl

theorem gfix_closed (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hH : MonoInfl H)
    (hN : ∀ y : CountableOrdinal, (veblenValue fix pow y).val ≤ (H y).val) (κ : CountableOrdinal)
    (hκ : orbit .base H zeroValue κ = κ) (hpos : 0 < κ.val) (y : CountableOrdinal)
    (hy : y.val < κ.val) : (H y).val < κ.val := by
  have hl := gfix_limit h1 h2 H hH hN κ hκ hpos
  have hy' : y.val < (orbit .base H zeroValue κ).val :=
    lt_of_lt_of_eq hy (congrArg Subtype.val hκ).symm
  obtain ⟨a, ha, hya⟩ := lt_orbit_limit H zeroValue κ hl y.val hy'
  obtain ⟨a1, ha1⟩ := countable_mk (a.val + 1) ((hl.add_one_lt ha).trans (countable_val_lt κ))
  have s1 : (H y).val ≤ (orbit .base H zeroValue a1).val := by
    rw [orbit_succ H zeroValue a a1 ha1]
    exact hH.1 y (orbit .base H zeroValue a) hya.le
  have s2 : (orbit .base H zeroValue a1).val < (orbit .base H zeroValue κ).val :=
    orbit_strictMono H zeroValue hH.2 a1 κ (by rw [ha1]; exact hl.add_one_lt ha)
  rw [hκ] at s2
  exact lt_of_le_of_lt s1 s2

theorem gfix_add_closed (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hH : MonoInfl H)
    (hN : ∀ y : CountableOrdinal, (veblenValue fix pow y).val ≤ (H y).val) (κ : CountableOrdinal)
    (hκ : orbit .base H zeroValue κ = κ) (hpos : 0 < κ.val) (y b : CountableOrdinal)
    (hy : y.val < κ.val) (hb : b.val < κ.val) : y.val + b.val < κ.val := by
  rcases le_total y.val b.val with h | h
  · exact lt_of_le_of_lt ((add_le_add h le_rfl).trans ((veblen_double h1 h2 b).trans (hN b)))
      (gfix_closed h1 h2 H hH hN κ hκ hpos b hb)
  · exact lt_of_le_of_lt ((add_le_add le_rfl h).trans ((veblen_double h1 h2 y).trans (hN y)))
      (gfix_closed h1 h2 H hH hN κ hκ hpos y hy)

theorem gfix_orbit_closed (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hH : MonoInfl H)
    (hN : ∀ y : CountableOrdinal, (veblenValue fix pow y).val ≤ (H y).val) (κ : CountableOrdinal)
    (hκ : orbit .base H zeroValue κ = κ) (hpos : 0 < κ.val) (y b : CountableOrdinal)
    (hy : y.val < κ.val) (hb : b.val < κ.val) : (orbit .base H y b).val < κ.val := by
  have hsum := gfix_add_closed h1 h2 H hH hN κ hκ hpos y b hy hb
  obtain ⟨yb, hyb⟩ := countable_mk (y.val + b.val) (hsum.trans (countable_val_lt κ))
  have s1 : (orbit .base H y b).val ≤ (orbit .base H (orbit .base H zeroValue y) b).val :=
    orbit_start_mono H hH.1 y (orbit .base H zeroValue y) (orbit_id_le H zeroValue hH.2 y) b
  have s2 : (orbit .base H (orbit .base H zeroValue y) b).val ≤ (orbit .base H zeroValue yb).val :=
    orbit_compose_le H hH zeroValue y b yb hyb
  have s3 : (orbit .base H zeroValue yb).val < (orbit .base H zeroValue κ).val :=
    orbit_strictMono H zeroValue hH.2 yb κ (by rw [hyb]; exact hsum)
  rw [hκ] at s3
  exact lt_of_le_of_lt (s1.trans s2) s3

/-- The orbit of a critical-preserving `H` from a critical start consists of critical values. -/
theorem orbit_crit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hH : MonoInfl H)
    (hC : ∀ x : CountableOrdinal, Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
      Critical (veblenValue fix pow) (baseValue fix pow w) (H x).val)
    (x : CountableOrdinal) (hx : Critical (veblenValue fix pow) (baseValue fix pow w) x.val) :
    ∀ a : CountableOrdinal,
      Critical (veblenValue fix pow) (baseValue fix pow w) (orbit .base H x a).val := by
  refine countable_induction _ ?_ ?_ ?_
  · intro a h0
    rw [orbit_zero H x a h0]
    exact hx
  · intro a' a ha ih
    rw [orbit_succ H x a' a ha]
    exact hC _ ih
  · intro l hl ih
    have hposl : 0 < (orbit .base H x l).val :=
      lt_of_lt_of_le hl.bot_lt (orbit_id_le H x hH.2 l)
    refine critLim h1 h2 (orbit .base H x l) hposl (fun y hy => ?_)
    obtain ⟨β, hβ, hyβ⟩ := lt_orbit_limit H x l hl y.val hy
    exact ⟨orbit .base H x β, ih β hβ, hyβ, orbit_le_limit H x l hl β hβ⟩

/-! Composites of one step. -/

theorem step_composite_up (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (π : Ordinal.{0})
    (H : CountableOrdinal → CountableOrdinal) (hP : NormPrincipal π) (hH : MonoInfl H)
    (hC : ∀ x : CountableOrdinal, Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
      Critical (veblenValue fix pow) (baseValue fix pow w) (H x).val)
    (hUp : StepUp fix pow w π H) (a : CountableOrdinal) :
    StepUp fix pow w (π * a.val) (fun x => orbit .base H x a) := by
  intro ζ x hctx hx hψ
  have bnd : ∀ b : CountableOrdinal, b.val ≤ a.val → ζ + π * b.val ≤ endpoint :=
    fun b hb => le_trans ((add_le_add_iff_left ζ).2 (mul_le_mul' le_rfl hb)) hctx.1
  have crit := orbit_crit h1 h2 H hH hC x hx
  have chain : ∀ b : CountableOrdinal, b.val ≤ a.val →
      psiO fix pow w (ζ + π * b.val) ≤ (orbit .base H x b).val := by
    refine countable_induction _ ?_ ?_ ?_
    · intro b h0 _
      rw [orbit_zero H x b h0, h0, mul_zero, add_zero]
      exact hψ
    · intro b' b hb ihb hba
      have hb'b : b'.val ≤ b.val := by rw [hb]; exact le_self_add
      have hstep : b'.val + 1 ≤ a.val := by rw [← hb]; exact hba
      have hc := ctx_step hP hctx (countable_val_lt b') hstep
      have e1 : ζ + π * b'.val + π = ζ + π * b.val := by rw [hb, mul_add_one, add_assoc]
      have key := hUp (ζ + π * b'.val) (orbit .base H x b') hc (crit b') (ihb (hb'b.trans hba))
      rw [e1] at key
      rw [orbit_succ H x b' b hb]
      exact key
    · intro l hl ihl hla
      refine psiO_least h1 h2 (bnd l hla) _ (crit l) (fun η hη _ => ?_)
      obtain ⟨b', hb', hlt⟩ : ∃ b' : CountableOrdinal, b'.val < l.val ∧ η < ζ + π * b'.val := by
        rcases lt_or_ge η ζ with h | h
        · exact ⟨zeroValue, hl.bot_lt, lt_of_lt_of_le h le_self_add⟩
        · have hsub : η - ζ < π * l.val := (Ordinal.sub_lt_of_le h).2 hη
          obtain ⟨c', hc'l, hc'⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit hl).1 hsub
          obtain ⟨b', hb'⟩ := countable_mk c' (hc'l.trans (countable_val_lt l))
          refine ⟨b', by rw [hb']; exact hc'l, ?_⟩
          rw [hb']
          exact lt_of_eq_of_lt (Ordinal.add_sub_cancel_of_le h).symm
            ((add_lt_add_iff_left ζ).2 hc')
      have hb'a : b'.val ≤ a.val := le_trans hb'.le hla
      exact lt_of_le_of_lt ((psiO_mono h1 h2 (bnd b' hb'a) hlt.le).trans (ihl b' hb' hb'a))
        (orbit_strictMono H x hH.2 b' l hb')
  exact chain a le_rfl

theorem step_composite_low (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (π : Ordinal.{0})
    (H : CountableOrdinal → CountableOrdinal) (hP : NormPrincipal π) (hH : MonoInfl H)
    (hLow : StepLow fix pow w π H) (a : CountableOrdinal) (ha1 : 1 ≤ a.val) :
    StepLow fix pow w (π * a.val) (fun x => orbit .base H x a) := by
  intro ζ x hctx hnorm hπθ hx
  have hend : ζ + π * a.val ≤ endpoint := hctx.1
  have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
  rw [np_norm_mul hP ha0 (countable_val_lt a)] at hπθ
  have haθ : a.val < psiO fix pow w (ζ + π * a.val) := lt_of_le_of_lt (le_max_left _ _) hπθ
  have hπ'θ : coefficientNorm π < psiO fix pow w (ζ + π * a.val) :=
    lt_of_le_of_lt (le_max_right _ _) hπθ
  have bnd : ∀ b : CountableOrdinal, b.val ≤ a.val → ζ + π * b.val ≤ endpoint :=
    fun b hb => le_trans ((add_le_add_iff_left ζ).2 (mul_le_mul' le_rfl hb)) hctx.1
  have chain : ∀ b : CountableOrdinal, b.val ≤ a.val →
      (orbit .base H x b).val ≤ psiO fix pow w (ζ + π * b.val) := by
    refine countable_induction _ ?_ ?_ ?_
    · intro b h0 _
      rw [orbit_zero H x b h0, h0, mul_zero, add_zero]
      exact hx
    · intro b' b hb ihb hba
      have hb'b : b'.val ≤ b.val := by rw [hb]; exact le_self_add
      have hstep : b'.val + 1 ≤ a.val := by rw [← hb]; exact hba
      have hb'lt : b'.val < a.val := lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl) hstep
      have hb1 : 1 ≤ b.val := by rw [hb]; exact le_add_self
      have hc := ctx_step hP hctx (countable_val_lt b') hstep
      have e1 : ζ + π * b'.val + π = ζ + π * b.val := by rw [hb, mul_add_one, add_assoc]
      have act : coefficientNorm (ζ + π * b'.val) < psiO fix pow w (ζ + π * b.val) ∧
          coefficientNorm π < psiO fix pow w (ζ + π * b.val) := by
        by_contra hcon
        have hM : psiO fix pow w (ζ + π * b.val) ≤
            max (coefficientNorm ζ) (max b.val (coefficientNorm π)) := by
          rcases not_and_or.1 hcon with h | h
          · exact (not_lt.1 h).trans ((ctx_norm_le hP hctx (countable_val_lt b') hb'lt).trans
              (max_le_max le_rfl (max_le_max hb'b le_rfl)))
          · exact (not_lt.1 h).trans ((le_max_right _ _).trans (le_max_right _ _))
        have hle : ζ + π * b.val ≤ ζ + π * a.val :=
          (add_le_add_iff_left ζ).2 (mul_le_mul' le_rfl hba)
        have hstall : psiO fix pow w (ζ + π * a.val) = psiO fix pow w (ζ + π * b.val) := by
          refine psiO_stall h1 h2 hend hle (fun η hge hlt => hM.trans ?_)
          have hζη : ζ ≤ η := le_self_add.trans hge
          have hητ : ζ + (η - ζ) = η := Ordinal.add_sub_cancel_of_le hζη
          have hτ : η - ζ < π * a.val := (Ordinal.sub_lt_of_le hζη).2 hlt
          have hτΩ : η - ζ < π * omegaIndex :=
            lt_trans hτ (mul_lt_mul_of_pos_left (countable_val_lt a) hP.1)
          have hle' : π * b.val ≤ η - ζ := (Ordinal.le_sub_of_le hζη).2 hge
          have nf := np_ge hP hb1 hle' hτΩ
          have hs := hctx.2 (η - ζ) hτ
          rw [hητ] at hs
          rw [hs]
          exact max_le_max le_rfl nf
        rw [hstall] at hnorm haθ hπ'θ
        exact absurd hM (not_le.2 (max_lt hnorm (max_lt (lt_of_le_of_lt hba haθ) hπ'θ)))
      have key := hLow (ζ + π * b'.val) (orbit .base H x b') hc
      rw [e1] at key
      rw [orbit_succ H x b' b hb]
      exact key act.1 act.2 (ihb (hb'b.trans hba))
    · intro l hl ihl hla
      refine orbit_limit_le H x l hl _ (fun β hβ => ?_)
      exact (ihl β hβ (le_trans hβ.le hla)).trans (psiO_mono h1 h2 (bnd l hla)
        ((add_le_add_iff_left ζ).2 (mul_le_mul' le_rfl hβ.le)))
  exact chain a le_rfl

end

theorem stepSuccessor : StepSuccessor := by
  intro Z s add mul w one pow fix h1 h2 π H hP hπΩ hH hN hC hUp hLow
  refine stepDiagonal Z s add mul w one pow fix h1 h2 (fun a => π * a.val) (π * omegaIndex)
    (fun a x => orbit .base H x a) (towerValue fix 0 H) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun a _ => step_composite_up h1 h2 π H hP hH hC hUp a
  · exact fun a ha => step_composite_low h1 h2 π H hP hH hLow a ha
  · exact fun a => mul_lt_mul_of_pos_left (countable_val_lt a) hP.1
  · intro τ hτ
    obtain ⟨b0, hb0Ω, hb0n, hτb⟩ := np_div_le hP hτ
    obtain ⟨a, ha⟩ := countable_mk b0 hb0Ω
    obtain ⟨b, hb⟩ := countable_mk (a.val + 1)
      ((isSuccLimit_omega 1).add_one_lt (countable_val_lt a))
    refine ⟨a, b, hb, by rw [ha]; exact hb0n, ?_⟩
    show τ < π * b.val
    rw [hb, ha]
    exact hτb
  · intro a ha1
    have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
    show coefficientNorm (π * a.val) ≤ max (coefficientNorm (π * omegaIndex)) a.val
    rw [np_norm_mul hP ha0 (countable_val_lt a)]
    exact max_le (le_max_right _ _) (hπΩ.trans (le_max_left _ _))
  · intro a τ ha1 hle hτ
    have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
    show coefficientNorm (π * a.val) ≤ coefficientNorm τ
    rw [np_norm_mul hP ha0 (countable_val_lt a)]
    exact np_ge hP ha1 hle hτ
  · exact fun a b x h => orbit_mono H x hH.2 h
  · exact fun a x y h => orbit_start_mono H hH.1 x y h a
  · exact fun a => orbit_id_le H zeroValue hH.2 a
  · exact fun l hl b Hb => orbit_limit_le H zeroValue l hl b Hb
  · intro κ hκ hpos
    exact ⟨gfix_limit h1 h2 H hH hN κ hκ hpos,
      fun a x ha hx => gfix_orbit_closed h1 h2 H hH hN κ hκ hpos x a hx ha⟩
  · intro κ hκ hΓκ
    have hκ' : orbit .base H zeroValue κ = κ := hκ
    have hpos : 0 < κ.val := lt_of_le_of_lt (ozl _) hΓκ
    have hl := gfix_limit h1 h2 H hH hN κ hκ' hpos
    refine critLim h1 h2 κ hpos (fun y hy => ?_)
    have hy' : y.val < (orbit .base H zeroValue κ).val :=
      lt_of_lt_of_eq hy (congrArg Subtype.val hκ').symm
    obtain ⟨a, ha, hya⟩ := lt_orbit_limit H zeroValue κ hl y.val hy'
    refine ⟨orbit .base H (baseValue fix pow w) a,
      orbit_crit h1 h2 H hH hC (baseValue fix pow w) crit_base a, ?_, ?_⟩
    · exact lt_of_lt_of_le hya
        (orbit_start_mono H hH.1 zeroValue (baseValue fix pow w) (ozl _) a)
    · exact (gfix_orbit_closed h1 h2 H hH hN κ hκ' hpos (baseValue fix pow w) a hΓκ ha).le
  · intro x
    rw [b0_eq]
    exact fixLeastAbove Z s add mul w one pow fix h1 h2 (fun α => orbit .base H zeroValue α)
      (fun x y hxy => orbit_mono H zeroValue hH.2 hxy)
      (fun x => orbit_id_le H zeroValue hH.2 x)
      (fun l hl => orbit_limit_eq H zeroValue l hl) x

#print axioms stepSuccessor

end LogicLineages.PersistentMarking.ActualCalibrationStep
