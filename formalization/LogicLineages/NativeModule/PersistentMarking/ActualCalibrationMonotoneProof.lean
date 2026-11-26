module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseAssemblyProof

@[expose] public section

/-! Layer 1. Generic full-prefix orbit facts (start-monotonicity, composition), and
monotonicity of the semantic `Next`, `B_0` and `N_B`. Continuity is NOT claimed: `Next` (least
epsilon above) jumps at epsilon numbers, and none of the arguments below uses continuity of the
iterated function, only the limit clause of the orbit itself. -/

namespace LogicLineages.PersistentMarking.ActualCalibration
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse
open scoped Ordinal

/-- Induction over countable ordinals by zero / successor / limit. -/
theorem countable_induction (P : CountableOrdinal → Prop)
    (zero : ∀ α : CountableOrdinal, α.val = 0 → P α)
    (succ : ∀ α β : CountableOrdinal, β.val = α.val + 1 → P α → P β)
    (limit : ∀ l : CountableOrdinal, Order.IsSuccLimit l.val →
      (∀ β : CountableOrdinal, β.val < l.val → P β) → P l) :
    ∀ α, P α := by
  have claim : ∀ a : Ordinal.{0}, ∀ α : CountableOrdinal, α.val = a → P α := by
    intro a
    refine Ordinal.induction (p := fun a => ∀ α : CountableOrdinal, α.val = a → P α) a (fun a ih => ?_)
    intro α hα
    rcases zero_or_succ_or_isSuccLimit a with h0 | ⟨c, hc⟩ | hl
    · exact zero α (hα.trans h0)
    · have hca : c < a := by rw [← hc]; exact Order.lt_succ c
      let γ := mkCountable c (hca.trans (hα ▸ countable_val_lt α))
      exact succ γ α (by rw [hα, ← hc, Ordinal.add_one_eq_succ]; rfl) (ih c hca γ rfl)
    · exact limit α (hα ▸ hl) (fun β hβ => ih β.val (hα ▸ hβ) β rfl)
  intro α
  exact claim α.val α rfl

theorem orbit_succ (f : CountableOrdinal → CountableOrdinal) (x : CountableOrdinal)
    (α β : CountableOrdinal) (h : β.val = α.val + 1) : orbit .base f x β = f (orbit .base f x α) :=
  (orbitEquations .base f x).2.1 α β h

theorem orbit_limit_eq (f : CountableOrdinal → CountableOrdinal) (x : CountableOrdinal)
    (l : CountableOrdinal) (hl : Order.IsSuccLimit l.val) :
    (orbit .base f x l).val = ⨆ e : EarlierStages l, (orbit .base f x (earlierStage l e)).val :=
  (orbitEquations .base f x).2.2 l hl

/-- Start-monotonicity: a monotone `f` has orbits monotone in the starting point. -/
theorem orbit_start_mono (f : CountableOrdinal → CountableOrdinal)
    (hf : ∀ x y : CountableOrdinal, x.val ≤ y.val → (f x).val ≤ (f y).val)
    (x y : CountableOrdinal) (hxy : x.val ≤ y.val) :
    ∀ α, (orbit .base f x α).val ≤ (orbit .base f y α).val := by
  refine countable_induction _ ?_ ?_ ?_
  · intro α h0
    rw [orbit_zero f x α h0, orbit_zero f y α h0]
    exact hxy
  · intro α β h ih
    rw [orbit_succ f x α β h, orbit_succ f y α β h]
    exact hf _ _ ih
  · intro l hl ih
    rw [orbit_limit_eq f x l hl, orbit_limit_eq f y l hl]
    refine ciSup_le' (fun e => (ih _ e.property).trans ?_)
    exact le_ciSup (bddAbove_orbit .base f (fun e : EarlierStages l => orbit .base f y (earlierStage l e))) e

/-- Composition (one direction): `f^β(f^α(x)) ≤ f^(α+β)(x)` for monotone inflationary `f`. -/
theorem orbit_compose_le (f : CountableOrdinal → CountableOrdinal) (hf : MonoInfl f)
    (x α : CountableOrdinal) :
    ∀ β γ : CountableOrdinal, γ.val = α.val + β.val →
      (orbit .base f (orbit .base f x α) β).val ≤ (orbit .base f x γ).val := by
  refine countable_induction (fun β => ∀ γ : CountableOrdinal, γ.val = α.val + β.val →
    (orbit .base f (orbit .base f x α) β).val ≤ (orbit .base f x γ).val) ?_ ?_ ?_
  · intro β h0 γ hγ
    rw [orbit_zero f _ β h0]
    have : γ = α := Subtype.ext (by rw [hγ, h0, add_zero])
    rw [this]
  · intro β' β h ih γ hγ
    have lt : α.val + β'.val < γ.val := by
      rw [hγ, h, ← add_assoc]
      exact Order.lt_add_one_iff.2 le_rfl
    let γ' := mkCountable (α.val + β'.val) (lt.trans (countable_val_lt γ))
    rw [orbit_succ f _ β' β h, orbit_succ f x γ' γ (by rw [hγ, h, ← add_assoc]; rfl)]
    exact hf.1 _ _ (ih γ' rfl)
  · intro l hl ih γ hγ
    rw [orbit_limit_eq f _ l hl]
    refine ciSup_le' (fun e => ?_)
    have lt : α.val + e.val < γ.val := by rw [hγ]; exact add_lt_add_right e.property _
    let γe := mkCountable (α.val + e.val) (lt.trans (countable_val_lt γ))
    exact (ih (earlierStage l e) e.property γe rfl).trans (orbit_mono f x hf.2 lt.le)

/-! The semantic building blocks. -/

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

/-- `fix f` is monotone and inflationary for every monotone `f`. -/
theorem fix_monoInfl (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (f : CountableOrdinal → CountableOrdinal)
    (hf : ∀ x y : CountableOrdinal, x.val ≤ y.val → (f x).val ≤ (f y).val) : MonoInfl (fix f) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · rw [h2.2.2.2.2 f x, h2.2.2.2.2 f y]
    refine orbit_start_mono f hf _ _ ?_ w
    rw [h1.2.1 x, h1.2.1 y]
    exact add_le_add hxy le_rfl
  · have wlim : Order.IsSuccLimit w.val := by rw [h2.1]; exact isSuccLimit_omega0
    let z0 := mkCountable 0 zero_lt_omegaOne
    have hz0 : z0.val < w.val := by rw [h2.1]; exact omega0_pos
    have le := orbit_le_limit f (s z) w wlim z0 hz0
    rw [orbit_zero f (s z) z0 rfl] at le
    rw [h2.2.2.2.2 f z]
    refine lt_of_lt_of_le ?_ le
    rw [h1.2.1 z]
    exact Order.lt_add_one_iff.2 le_rfl

/-- The value of `fix f z` dominates `f` at stage one: `f (s z) ≤ fix f z`. -/
theorem fix_ge_stage_one (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (f : CountableOrdinal → CountableOrdinal) (z : CountableOrdinal) :
    (f (s z)).val ≤ (fix f z).val := by
  have wlim : Order.IsSuccLimit w.val := by rw [h2.1]; exact isSuccLimit_omega0
  let z0 := mkCountable 0 zero_lt_omegaOne
  let o1 := mkCountable 1 one_lt_index
  have h1lt : o1.val < w.val := by rw [h2.1]; exact one_lt_omega0
  have le := orbit_le_limit f (s z) w wlim o1 h1lt
  rw [orbit_succ f (s z) z0 o1 (by show (1 : Ordinal.{0}) = 0 + 1; simp), orbit_zero f (s z) z0 rfl] at le
  rw [h2.2.2.2.2 f z]
  exact le

theorem next_monoInfl (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : MonoInfl (fix pow) := by
  refine fix_monoInfl h1 h2 pow (fun x y hxy => ?_)
  rw [(h2.2.2.2.1 x).2, (h2.2.2.2.1 y).2]
  exact Ordinal.opow_le_opow_right omega0_pos hxy

theorem b0_monoInfl (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (h : CountableOrdinal → CountableOrdinal)
    (hh : MonoInfl h) :
    MonoInfl (towerValue fix 0 h) ∧ ∀ x, (h x).val ≤ (towerValue fix 0 h x).val := by
  rw [NativeTowerProof.towerValue_zero]
  let G : CountableOrdinal → CountableOrdinal := fun α => orbit (tier 0) h zeroValue α
  have hG : ∀ x y : CountableOrdinal, x.val ≤ y.val → (G x).val ≤ (G y).val :=
    fun x y hxy => orbit_mono h zeroValue hh.2 hxy
  refine ⟨fix_monoInfl h1 h2 G hG, fun x => ?_⟩
  refine le_trans ?_ (fix_ge_stage_one h2 G x)
  show (h x).val ≤ (orbit .base h zeroValue (s x)).val
  rw [orbit_succ h zeroValue x (s x) (h1.2.1 x)]
  exact hh.1 _ _ (orbit_id_le h zeroValue hh.2 x)

/-- The `A_1`-orbit of `B_0` from `Next` consists of monotone inflationary functions and is
pointwise monotone in the stage. -/
theorem b0Orbit_mono (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ β : CountableOrdinal, MonoInfl (orbit (tier 1) (towerValue fix 0) (fix pow) β) ∧
      ∀ α : CountableOrdinal, α.val ≤ β.val → ∀ x,
        (orbit (tier 1) (towerValue fix 0) (fix pow) α x).val ≤
          (orbit (tier 1) (towerValue fix 0) (fix pow) β x).val := by
  have eqs := orbitEquations (tier 1) (towerValue fix 0) (fix pow)
  refine countable_induction _ ?_ ?_ ?_
  · intro β h0
    rw [eqs.1 β h0]
    refine ⟨next_monoInfl h1 h2, fun α hα x => ?_⟩
    have : α = β := Subtype.ext (by rw [h0]; exact le_antisymm (h0 ▸ hα) (not_lt.mp not_lt_zero))
    rw [this, eqs.1 β h0]
  · intro α' β h ih
    rw [eqs.2.1 α' β h]
    obtain ⟨mi, ge⟩ := b0_monoInfl h1 h2 _ ih.1
    refine ⟨mi, fun α hα x => ?_⟩
    rcases hα.lt_or_eq with hlt | heq
    · have : α.val ≤ α'.val := by
        rw [h] at hlt
        exact Order.lt_add_one_iff.1 hlt
      exact (ih.2 α this x).trans (ge x)
    · have : α = β := Subtype.ext heq
      rw [this, eqs.2.1 α' β h]
  · intro l hl ih
    have sup : ∀ x, (orbit (tier 1) (towerValue fix 0) (fix pow) l x).val =
        ⨆ e : EarlierStages l, (orbit (tier 1) (towerValue fix 0) (fix pow) (earlierStage l e) x).val :=
      fun x => eqs.2.2 l hl x
    have bdd : ∀ x, BddAbove (Set.range (fun e : EarlierStages l =>
        (orbit (tier 1) (towerValue fix 0) (fix pow) (earlierStage l e) x).val)) := fun x =>
      bddAbove_orbit .base id (fun e : EarlierStages l =>
        orbit (tier 1) (towerValue fix 0) (fix pow) (earlierStage l e) x)
    let e0 : EarlierStages l := ⟨0, hl.bot_lt⟩
    refine ⟨⟨fun x y hxy => ?_, fun x => ?_⟩, fun α hα x => ?_⟩
    · rw [sup x, sup y]
      exact ciSup_le' (fun e => ((ih _ e.property).1.1 x y hxy).trans (le_ciSup (bdd y) e))
    · rw [sup x]
      exact ((ih _ e0.property).1.2 x).trans_le (le_ciSup (bdd x) e0)
    · rcases hα.lt_or_eq with hlt | heq
      · rw [sup x]
        have e : earlierStage l ⟨α.val, hlt⟩ = α := Subtype.ext rfl
        have := le_ciSup (bdd x) ⟨α.val, hlt⟩
        rw [e] at this
        exact this
      · have : α = l := Subtype.ext heq
        rw [this]

theorem veblen_eq_fix :
    veblenValue fix pow = fix (fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue) :=
  NativeTowerProof.towerValue_one fix (towerValue fix 0) (fix pow)

theorem veblen_monoInfl (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : MonoInfl (veblenValue fix pow) := by
  rw [veblen_eq_fix]
  exact fix_monoInfl h1 h2 _ (fun α β hαβ => ((b0Orbit_mono h1 h2) β).2 α hαβ zeroValue)

end

theorem monotoneLayer : MonotoneLayer := by
  intro Z s add mul w one pow fix h1 h2
  exact ⟨next_monoInfl h1 h2, fun h hh => b0_monoInfl h1 h2 h hh, veblen_monoInfl h1 h2⟩

end LogicLineages.PersistentMarking.ActualCalibration
