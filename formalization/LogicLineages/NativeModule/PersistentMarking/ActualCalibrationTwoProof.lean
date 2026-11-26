module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationComparisonProof
public import Mathlib.SetTheory.Ordinal.Principal

@[expose] public section

/-! Layer 3: `Δ_2' = ψ(Ω)`. With `F(β) = N_B^β(Γ_0)` (the critical enumeration) and
`G(α) = N_B^α(0)`, `Δ_2' = B_0 N_B Γ_0 = G^ω(Γ_0+1) =: δ`. Then `G(δ) ≤ δ`, `δ ≥ ω²`, so by the
orbit comparison `F(δ) ≤ G((ω+1)+δ) = G(δ) ≤ δ`: `δ` is critical, and `F` has no fixed point
below `δ`. On countable indices `|η| = η`, `F(η) ≤ ψ(η)` below `δ` and `ψ(η) ≤ F(η)` always, whence
`ψ(Ω) = δ`. -/

namespace LogicLineages.PersistentMarking.ActualCalibration
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets
open OrdinalNativeOrbitProof OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse
open scoped Ordinal

theorem countable_strong_induction (P : CountableOrdinal → Prop)
    (h : ∀ η : CountableOrdinal, (∀ η' : CountableOrdinal, η'.val < η.val → P η') → P η) : ∀ η, P η := by
  have claim : ∀ a : Ordinal.{0}, ∀ η : CountableOrdinal, η.val = a → P η := by
    intro a
    refine Ordinal.induction (p := fun a => ∀ η : CountableOrdinal, η.val = a → P η) a (fun a ih => ?_)
    intro η hη
    exact h η (fun η' hlt => ih η'.val (hη ▸ hlt) η' rfl)
  intro η
  exact claim η.val η rfl

theorem norm_countable (η : Ordinal.{0}) (h : η < ω₁) : coefficientNorm η = η := by
  rcases eq_or_ne η 0 with rfl | h0
  · rw [norm_eq, CNF.zero_right]
    rfl
  · have h' : η < omegaIndex := h
    rw [norm_eq, CNF.of_lt h0 h']
    have n0 : coefficientNorm 0 = 0 := by rw [norm_eq, CNF.zero_right]; rfl
    simp [n0]

theorem calibrationTwo : CalibrationTwo := by
  intro Z s add mul w one pow fix h1 h2
  let N := veblenValue fix pow
  let Γ := baseValue fix pow w
  have mi : MonoInfl N := veblen_monoInfl h1 h2
  obtain ⟨infl, hΓ⟩ := veblenInflationary Z s add mul w one pow fix h1 h2
  have char : CharacterizationP (actualData N Γ) := actualCharacterization N Γ infl hΓ
  let F := fun β => orbit .base N Γ β
  let G : CountableOrdinal → CountableOrdinal := fun α => orbit .base N zeroValue α
  have Gmono : ∀ x y : CountableOrdinal, x.val ≤ y.val → (G x).val ≤ (G y).val :=
    fun x y hxy => orbit_mono N zeroValue infl hxy
  have wlim : Order.IsSuccLimit w.val := by rw [h2.1]; exact isSuccLimit_omega0
  -- δ = Δ_2'
  let δc := orbit .base G (s Γ) w
  have delta : sequenceValue fix pow w 2 = δc := by
    show towerValue fix 0 N Γ = _
    rw [NativeTowerProof.towerValue_zero]
    exact h2.2.2.2.2 G Γ
  have stages : ∀ e : EarlierStages w, (orbit .base G (s Γ) (earlierStage w e)).val ≤ δc.val :=
    fun e => orbit_le_limit G (s Γ) w wlim (earlierStage w e) e.property
  haveI : Nonempty (EarlierStages w) := ⟨⟨0, by rw [h2.1]; exact omega0_pos⟩⟩
  have supEq := orbit_limit_eq G (s Γ) w wlim
  have bddS := bddAbove_orbit .base G (fun e : EarlierStages w => orbit .base G (s Γ) (earlierStage w e))
  -- the next stage stays below δ
  have nextStage : ∀ e : EarlierStages w, (G (orbit .base G (s Γ) (earlierStage w e))).val ≤ δc.val := by
    intro e
    have hlt : e.val + 1 < w.val := wlim.add_one_lt e.property
    let e1 := mkCountable (e.val + 1) (hlt.trans (countable_val_lt w))
    rw [← orbit_succ G (s Γ) (earlierStage w e) e1 rfl]
    exact orbit_le_limit G (s Γ) w wlim e1 hlt
  have belowStage : ∀ y : CountableOrdinal, (∃ e : EarlierStages w,
      y.val ≤ (orbit .base G (s Γ) (earlierStage w e)).val) → (G y).val ≤ δc.val := by
    rintro y ⟨e, he⟩
    exact (Gmono _ _ he).trans (nextStage e)
  -- G(δ) ≤ δ
  have Gdelta : (G δc).val ≤ δc.val := by
    rcases zero_or_succ_or_isSuccLimit δc.val with h0 | ⟨c, hc⟩ | hl
    · exfalso
      have := stages ⟨0, omega0_pos.trans_eq h2.1.symm⟩
      rw [orbit_zero G (s Γ) _ rfl, h0, h1.2.1 Γ] at this
      exact absurd this (not_le.2 (Order.lt_add_one_iff.2 (not_lt.mp not_lt_zero)))
    · have hcl : c < δc.val := by rw [← hc]; exact Order.lt_succ c
      rw [supEq] at hcl
      obtain ⟨e, he⟩ := (lt_ciSup_iff bddS).1 hcl
      refine belowStage δc ⟨e, ?_⟩
      rw [← hc]
      exact Order.succ_le_of_lt he
    · show (orbit .base N zeroValue δc).val ≤ _
      rw [orbit_limit_eq N zeroValue δc hl]
      refine ciSup_le' (fun y => ?_)
      have hy := lt_of_lt_of_eq y.property supEq
      obtain ⟨e, he⟩ := (lt_ciSup_iff bddS).1 hy
      exact belowStage (earlierStage δc y) ⟨e, he.le⟩
  -- δ is large: Γ ≥ ω^ω ≥ ω²
  have Γbig : (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) ≤ Γ.val := by
    let g : CountableOrdinal → CountableOrdinal :=
      fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue
    have hN : N = fix g := veblen_eq_fix
    let z0 := mkCountable 0 zero_lt_omegaOne
    have g0 : g z0 = fix pow zeroValue := by
      show orbit (tier 1) (towerValue fix 0) (fix pow) z0 zeroValue = _
      rw [(orbitEquations (tier 1) (towerValue fix 0) (fix pow)).1 z0 rfl]
    have gmono : (g z0).val ≤ (g (s w)).val :=
      ((b0Orbit_mono h1 h2) (s w)).2 z0 (not_lt.mp not_lt_zero) zeroValue
    have step1 : (g (s w)).val ≤ Γ.val := by
      show _ ≤ (N w).val
      rw [hN]
      exact fix_ge_stage_one h2 g w
    -- Next(0) ≥ pow (pow (s 0)) = ω^ω
    have next0 : (ω : Ordinal.{0}) ^ (ω : Ordinal.{0}) ≤ (fix pow zeroValue).val := by
      let o1 := mkCountable 1 one_lt_index
      have two_lt : (2 : Ordinal.{0}) < ω := by exact_mod_cast nat_lt_omega0 2
      let o2 := mkCountable 2 (two_lt.trans omega0_lt_omega_one)
      have h2lt : o2.val < w.val := by
        rw [h2.1]
        exact two_lt
      have le := orbit_le_limit pow (s zeroValue) w wlim o2 h2lt
      rw [orbit_succ pow (s zeroValue) o1 o2 (by show (2 : Ordinal.{0}) = 1 + 1; exact one_add_one_eq_two.symm),
        orbit_succ pow (s zeroValue) z0 o1 (by show (1 : Ordinal.{0}) = 0 + 1; simp),
        orbit_zero pow (s zeroValue) z0 rfl] at le
      rw [h2.2.2.2.2 pow zeroValue]
      refine le_trans (le_of_eq ?_) le
      rw [(h2.2.2.2.1 _).2, (h2.2.2.2.1 _).2, h1.2.1 zeroValue]
      simp [zeroValue]
    have two_le : (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) ≤ ω ^ ω :=
      Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt (nat_lt_omega0 1))
    exact two_le.trans (next0.trans ((le_of_eq g0.symm).trans (gmono.trans step1)))
  have δbig : (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) ≤ δc.val := by
    have := stages ⟨0, omega0_pos.trans_eq h2.1.symm⟩
    rw [orbit_zero G (s Γ) _ rfl, h1.2.1 Γ] at this
    exact Γbig.trans ((Order.lt_add_one_iff.2 le_rfl).le.trans this)
  -- F(δ) = δ
  have absorb : (ω : Ordinal.{0}) + 1 + δc.val = δc.val := by
    have hlt : (ω : Ordinal.{0}) + 1 < ω ^ (2 : Ordinal.{0}) := by
      have hω : (ω : Ordinal.{0}) < ω ^ (2 : Ordinal.{0}) := left_lt_opow one_lt_omega0 one_lt_two
      exact isPrincipal_add_omega0_opow 2 hω (one_lt_omega0.trans hω)
    exact add_of_omega0_opow_le hlt δbig
  have Fdelta : (F δc).val = δc.val := by
    refine le_antisymm ?_ (orbit_id_le N Γ infl δc)
    have := orbitComparison Z s add mul w one pow fix h1 h2 δc δc absorb.symm
    exact this.trans Gdelta
  -- no fixed point of F below δ
  have noFix : ∀ θ : CountableOrdinal, θ.val < δc.val → θ.val < (F θ).val := by
    intro θ hθ
    refine lt_of_le_of_ne (orbit_id_le N Γ infl θ) (fun heq => ?_)
    have Gθ : (G θ).val = θ.val := by
      refine le_antisymm ?_ (orbit_id_le N zeroValue infl θ)
      have := orbit_start_mono N mi.1 zeroValue Γ (not_lt.mp not_lt_zero) θ
      exact this.trans heq.symm.le
    have Gfix : G θ = θ := Subtype.ext Gθ
    have const : ∀ α, orbit .base G θ α = θ := by
      refine countable_induction _ (fun α h0 => orbit_zero G θ α h0) (fun α β h ih => ?_) (fun l hl ih => ?_)
      · rw [orbit_succ G θ α β h, ih, Gfix]
      · apply Subtype.ext
        rw [orbit_limit_eq G θ l hl]
        refine le_antisymm (ciSup_le' (fun e => (congrArg Subtype.val (ih (earlierStage l e) e.property)).le)) ?_
        have := le_ciSup (bddAbove_orbit .base G (fun e : EarlierStages l => orbit .base G θ (earlierStage l e)))
          ⟨0, hl.bot_lt⟩
        rw [ih _ hl.bot_lt] at this
        exact this
    have Γθ : Γ.val < θ.val := by
      let z0 := mkCountable 0 zero_lt_omegaOne
      have hz : (F z0).val = Γ.val := by rw [show F z0 = Γ from orbit_zero N Γ z0 rfl]
      have hpos : z0.val < θ.val := by
        rcases eq_or_lt_of_le (not_lt.mp (not_lt_zero (a := θ.val)) : (0 : Ordinal.{0}) ≤ θ.val) with h | h
        · exfalso
          have hz' : θ = z0 := Subtype.ext h.symm
          rw [hz'] at heq
          rw [hz] at heq
          exact absurd (heq ▸ hΓ) (not_lt.2 zero_le_one)
        · exact h
      have := orbit_strictMono N Γ infl z0 θ hpos
      rw [hz] at this
      exact this.trans_eq heq.symm
    have sΓθ : (s Γ).val ≤ θ.val := by rw [h1.2.1 Γ]; exact Order.add_one_le_of_lt Γθ
    have bound := orbit_start_mono G Gmono (s Γ) θ sΓθ w
    rw [const w] at bound
    exact absurd (bound.trans_lt hθ) (lt_irrefl _)
  -- indices
  have ω1le : (ω₁ : Ordinal.{0}) ≤ endpoint := by
    have := (actualArgument 2).property
    have e2 : argument 2 = ω₁ := exact_LiteralRecurrence.2.2.2.1.trans exact_LiteralRecurrence.1
    rw [← e2]
    exact this
  let idx : CountableOrdinal → ActualIndex := fun η => ⟨η.val, (countable_val_lt η).le.trans ω1le⟩
  have normIdx : ∀ η : CountableOrdinal, actualNorm (idx η) = η.val :=
    fun η => norm_countable η.val (countable_val_lt η)
  let ψ := (actualData N Γ).psi
  have upper : ∀ η : CountableOrdinal, ψ (idx η) ≤ (F η).val := by
    refine countable_strong_induction _ (fun η ih => ?_)
    refine (char (idx η)).2.2 (F η).val ⟨η, rfl⟩ (fun η' hη' _ => ?_)
    let η'c := mkCountable η'.val (lt_trans (show η'.val < η.val from hη') (countable_val_lt η))
    have e : idx η'c = η' := Subtype.ext rfl
    rw [← e]
    exact (ih η'c hη').trans_lt (orbit_strictMono N Γ infl η'c η hη')
  have lower : ∀ η : CountableOrdinal, η.val < δc.val → (F η).val ≤ ψ (idx η) := by
    refine countable_strong_induction _ (fun η ih hη => ?_)
    obtain ⟨γ, hγ⟩ := (char (idx η)).1
    rcases lt_or_ge γ.val η.val with hlt | hge
    · exfalso
      have hγδ : γ.val < δc.val := hlt.trans hη
      have closure := (char (idx η)).2.1 (idx γ) hlt
        (show actualNorm (idx γ) < (actualData N Γ).psi (idx η) by rw [normIdx, ← hγ]; exact noFix γ hγδ)
      rw [← hγ] at closure
      exact absurd (ih γ hlt hγδ) (not_le.2 closure)
    · exact le_of_le_of_eq (orbit_mono N Γ infl hge) hγ
  -- ψ(Ω) = δ
  have argOmega : (actualArgument 2).val = ω₁ :=
    exact_LiteralRecurrence.2.2.2.1.trans exact_LiteralRecurrence.1
  have psiLe : ψ (actualArgument 2) ≤ δc.val := by
    refine (char (actualArgument 2)).2.2 δc.val ⟨δc, Fdelta⟩ (fun η' hη' hn => ?_)
    have hc : η'.val < ω₁ := argOmega ▸ hη'
    let η'c := mkCountable η'.val hc
    have e : idx η'c = η' := Subtype.ext rfl
    have hn' : η'c.val < δc.val := by
      have := normIdx η'c
      rw [e] at this
      rw [← this]
      exact hn
    rw [← e, ← Fdelta]
    exact (upper η'c).trans_lt (orbit_strictMono N Γ infl η'c δc hn')
  have psiGe : δc.val ≤ ψ (actualArgument 2) := by
    obtain ⟨β, hβ⟩ := (char (actualArgument 2)).1
    rcases lt_or_ge β.val δc.val with hlt | hge
    · exfalso
      have closure := (char (actualArgument 2)).2.1 (idx β)
        (show β.val < (actualArgument 2).val by rw [argOmega]; exact countable_val_lt β)
        (show actualNorm (idx β) < (actualData N Γ).psi (actualArgument 2) by
          rw [normIdx, ← hβ]; exact noFix β hlt)
      rw [← hβ] at closure
      exact absurd (lower β hlt) (not_le.2 closure)
    · rw [← Fdelta]
      exact le_of_le_of_eq (orbit_mono N Γ infl hge) hβ
  rw [delta]
  exact (le_antisymm psiLe psiGe).symm

#print axioms orbitComparison
#print axioms calibrationTwo

end LogicLineages.PersistentMarking.ActualCalibration
