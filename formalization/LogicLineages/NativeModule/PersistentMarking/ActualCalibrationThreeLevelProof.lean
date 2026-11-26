module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationTwoProof

@[expose] public section

/-! Layers T1–T3 for n = 3: the generic least-fixed-point property of `fix`, the reusable `B_0`
lemma (the n = 2 argument for an arbitrary monotone inflationary `h`), and the semantic level
invariant for `D β = B_0^β(N_B)`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

theorem orbit_const (g : CountableOrdinal → CountableOrdinal) (θ : CountableOrdinal) (hθ : g θ = θ) :
    ∀ α, orbit .base g θ α = θ := by
  refine countable_induction _ (fun α h0 => orbit_zero g θ α h0) (fun α β h ih => ?_) (fun l hl ih => ?_)
  · rw [orbit_succ g θ α β h, ih, hθ]
  · apply Subtype.ext
    rw [orbit_limit_eq g θ l hl]
    refine le_antisymm (ciSup_le' (fun e => (congrArg Subtype.val (ih (earlierStage l e) e.property)).le)) ?_
    have := le_ciSup (bddAbove_orbit .base g (fun e : EarlierStages l => orbit .base g θ (earlierStage l e)))
      ⟨0, hl.bot_lt⟩
    rw [ih _ hl.bot_lt] at this
    exact this

theorem fixLeastAbove : FixLeastAbove := by
  intro Z s add mul w one pow fix h1 h2 g gmono gid gcont x
  have wlim : Order.IsSuccLimit w.val := by rw [h2.1]; exact isSuccLimit_omega0
  haveI : Nonempty (EarlierStages w) := ⟨⟨0, by rw [h2.1]; exact omega0_pos⟩⟩
  have fixEq : fix g x = orbit .base g (s x) w := h2.2.2.2.2 g x
  let δc := orbit .base g (s x) w
  have supEq := orbit_limit_eq g (s x) w wlim
  have bddS := bddAbove_orbit .base g (fun e : EarlierStages w => orbit .base g (s x) (earlierStage w e))
  have stages : ∀ e : EarlierStages w, (orbit .base g (s x) (earlierStage w e)).val ≤ δc.val :=
    fun e => orbit_le_limit g (s x) w wlim (earlierStage w e) e.property
  have nextStage : ∀ e : EarlierStages w, (g (orbit .base g (s x) (earlierStage w e))).val ≤ δc.val := by
    intro e
    have hlt : e.val + 1 < w.val := wlim.add_one_lt e.property
    let e1 := mkCountable (e.val + 1) (hlt.trans (countable_val_lt w))
    rw [← orbit_succ g (s x) (earlierStage w e) e1 rfl]
    exact orbit_le_limit g (s x) w wlim e1 hlt
  have belowStage : ∀ y : CountableOrdinal, (∃ e : EarlierStages w,
      y.val ≤ (orbit .base g (s x) (earlierStage w e)).val) → (g y).val ≤ δc.val := by
    rintro y ⟨e, he⟩
    exact (gmono _ _ he).trans (nextStage e)
  have gδ : (g δc).val ≤ δc.val := by
    rcases zero_or_succ_or_isSuccLimit δc.val with h0 | ⟨c, hc⟩ | hl
    · exfalso
      have := stages ⟨0, omega0_pos.trans_eq h2.1.symm⟩
      rw [orbit_zero g (s x) _ rfl, h0, h1.2.1 x] at this
      exact absurd this (not_le.2 (Order.lt_add_one_iff.2 (not_lt.mp not_lt_zero)))
    · have hcl : c < δc.val := by rw [← hc]; exact Order.lt_succ c
      rw [supEq] at hcl
      obtain ⟨e, he⟩ := (lt_ciSup_iff bddS).1 hcl
      refine belowStage δc ⟨e, ?_⟩
      rw [← hc]
      exact Order.succ_le_of_lt he
    · rw [gcont δc hl]
      refine ciSup_le' (fun y => ?_)
      have hy := lt_of_lt_of_eq y.property supEq
      obtain ⟨e, he⟩ := (lt_ciSup_iff bddS).1 hy
      exact belowStage (earlierStage δc y) ⟨e, he.le⟩
  rw [fixEq]
  refine ⟨Subtype.ext (le_antisymm gδ (gid δc)), ?_, fun θ hθ gθ => ?_⟩
  · rw [← fixEq]
    exact (fix_monoInfl h1 h2 g gmono).2 x
  · have sxθ : (s x).val ≤ θ.val := by rw [h1.2.1 x]; exact Order.add_one_le_of_lt hθ
    have := orbit_start_mono g gmono (s x) θ sxθ w
    rw [orbit_const g θ gθ w] at this
    exact this

/-- `B_0 h x = fix (α ↦ h^α(0)) x`. -/
theorem b0_eq (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (h : CountableOrdinal → CountableOrdinal) :
    towerValue fix 0 h = fix (fun α => orbit .base h zeroValue α) :=
  NativeTowerProof.towerValue_zero fix h

theorem b0Lemma : B0Lemma := by
  intro Z s add mul w one pow fix h1 h2 h hh Γbig
  let Γ := h w
  let G : CountableOrdinal → CountableOrdinal := fun α => orbit .base h zeroValue α
  have Gmono : ∀ x y : CountableOrdinal, x.val ≤ y.val → (G x).val ≤ (G y).val :=
    fun x y hxy => orbit_mono h zeroValue hh.2 hxy
  obtain ⟨Gfix, Γlt, Gleast⟩ := fixLeastAbove Z s add mul w one pow fix h1 h2 G Gmono
    (fun x => orbit_id_le h zeroValue hh.2 x) (fun l hl => orbit_limit_eq h zeroValue l hl) Γ
  have hδ : towerValue fix 0 h Γ = fix G Γ := by rw [b0_eq]
  rw [hδ]
  let δc := fix G Γ
  have δbig : (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) ≤ δc.val := Γbig.trans Γlt.le
  have absorb : (ω : Ordinal.{0}) + 1 + δc.val = δc.val := by
    have hlt : (ω : Ordinal.{0}) + 1 < ω ^ (2 : Ordinal.{0}) := by
      have hω : (ω : Ordinal.{0}) < ω ^ (2 : Ordinal.{0}) := left_lt_opow one_lt_omega0 one_lt_two
      exact isPrincipal_add_omega0_opow 2 hω (one_lt_omega0.trans hω)
    exact add_of_omega0_opow_le hlt δbig
  -- comparison: h^β(Γ) ≤ h^((ω+1)+β)(0)
  have hω1 : (ω : Ordinal.{0}) + 1 < ω₁ := (isSuccLimit_omega 1).add_one_lt omega0_lt_omega_one
  let ωc := mkCountable ω omega0_lt_omega_one
  let ω1c := mkCountable (ω + 1) hω1
  have start : Γ.val ≤ (orbit .base h zeroValue ω1c).val := by
    rw [orbit_succ h zeroValue ωc ω1c rfl]
    refine hh.1 _ _ ?_
    rw [h2.1]
    exact orbit_id_le h zeroValue hh.2 ωc
  have compare : ∀ β γ : CountableOrdinal, γ.val = (ω + 1) + β.val →
      (orbit .base h Γ β).val ≤ (orbit .base h zeroValue γ).val := fun β γ hγ =>
    (orbit_start_mono h hh.1 _ _ start β).trans (orbit_compose_le h hh zeroValue ω1c β γ hγ)
  have Fδ : (orbit .base h Γ δc).val = δc.val := by
    refine le_antisymm ?_ (orbit_id_le h Γ hh.2 δc)
    have := compare δc δc absorb.symm
    exact this.trans (le_of_eq (congrArg Subtype.val Gfix))
  refine ⟨Fδ, fun θ hθ => ?_⟩
  refine lt_of_le_of_ne (orbit_id_le h Γ hh.2 θ) (fun heq => ?_)
  have Gθ : G θ = θ := by
    apply Subtype.ext
    refine le_antisymm ?_ (orbit_id_le h zeroValue hh.2 θ)
    exact (orbit_start_mono h hh.1 zeroValue Γ (not_lt.mp not_lt_zero) θ).trans heq.symm.le
  have Γθ : Γ.val < θ.val := by
    let z0 := mkCountable 0 zero_lt_omegaOne
    have hz : orbit .base h Γ z0 = Γ := orbit_zero h Γ z0 rfl
    rcases eq_or_lt_of_le (not_lt.mp (not_lt_zero (a := θ.val)) : (0 : Ordinal.{0}) ≤ θ.val) with h0 | hpos
    · exfalso
      have hz' : θ = z0 := Subtype.ext h0.symm
      rw [hz', hz] at heq
      have : (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) ≤ z0.val := heq ▸ Γbig
      exact absurd this (not_le.2 (show z0.val < (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) from opow_pos _ omega0_pos))
    · have := orbit_strictMono h Γ hh.2 z0 θ hpos
      rw [hz] at this
      exact this.trans_eq heq.symm
  exact absurd (Gleast θ Γθ Gθ) (not_le.2 hθ)

/-- `A_1`-orbit of `B_0` from any monotone inflationary start. -/
theorem b0Orbit_mono_from {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
    {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
    {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
    {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}
    (h1 : OrdinalArithmeticEquations Z s add mul) (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (h0 : CountableOrdinal → CountableOrdinal) (hh0 : MonoInfl h0) :
    ∀ β : CountableOrdinal, MonoInfl (orbit (tier 1) (towerValue fix 0) h0 β) ∧
      ∀ α : CountableOrdinal, α.val ≤ β.val → ∀ x,
        (orbit (tier 1) (towerValue fix 0) h0 α x).val ≤ (orbit (tier 1) (towerValue fix 0) h0 β x).val := by
  have eqs := orbitEquations (tier 1) (towerValue fix 0) h0
  refine countable_induction _ ?_ ?_ ?_
  · intro β h0β
    rw [eqs.1 β h0β]
    refine ⟨hh0, fun α hα x => ?_⟩
    have : α = β := Subtype.ext (by rw [h0β]; exact le_antisymm (h0β ▸ hα) (not_lt.mp not_lt_zero))
    rw [this, eqs.1 β h0β]
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
    have sup : ∀ x, (orbit (tier 1) (towerValue fix 0) h0 l x).val =
        ⨆ e : EarlierStages l, (orbit (tier 1) (towerValue fix 0) h0 (earlierStage l e) x).val :=
      fun x => eqs.2.2 l hl x
    have bdd : ∀ x, BddAbove (Set.range (fun e : EarlierStages l =>
        (orbit (tier 1) (towerValue fix 0) h0 (earlierStage l e) x).val)) := fun x =>
      bddAbove_orbit .base id (fun e : EarlierStages l => orbit (tier 1) (towerValue fix 0) h0 (earlierStage l e) x)
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

theorem levelInvariant : LevelInvariant := by
  intro Z s add mul w one pow fix h1 h2
  have base := b0Orbit_mono_from h1 h2 (veblenValue fix pow) (veblen_monoInfl h1 h2)
  refine ⟨fun β => (base β).1, fun α β hαβ x => (base β).2 α hαβ x, fun β β' hβ x => ?_⟩
  have mi := (base β).1
  have step : level fix pow β' = towerValue fix 0 (level fix pow β) :=
    (orbitEquations (tier 1) (towerValue fix 0) (veblenValue fix pow)).2.1 β β' hβ
  let E : CountableOrdinal → CountableOrdinal := fun α => orbit .base (level fix pow β) zeroValue α
  have r := fixLeastAbove Z s add mul w one pow fix h1 h2 E
    (fun x y hxy => orbit_mono (level fix pow β) zeroValue mi.2 hxy)
    (fun x => orbit_id_le (level fix pow β) zeroValue mi.2 x)
    (fun l hl => orbit_limit_eq (level fix pow β) zeroValue l hl) x
  rw [step, b0_eq]
  exact r

#print axioms fixLeastAbove
#print axioms b0Lemma
#print axioms levelInvariant

end LogicLineages.PersistentMarking.ActualCalibrationThree
