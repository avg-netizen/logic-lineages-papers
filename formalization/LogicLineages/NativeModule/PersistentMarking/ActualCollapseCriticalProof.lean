module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseNormProof
public import LogicLineages.NativeModule.PersistentMarking.NativeTowerProof
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! Criticality layer: for an inflationary `N` the full-prefix orbit `N^α(Γ)` is strictly
increasing, so the critical values exceed `Γ`, are countable, are unbounded below `ω₁`, and are
closed under suprema of increasing sequences; the paper's `N_B` is inflationary. -/

namespace LogicLineages.PersistentMarking.ActualCollapse
open Ordinal Cardinal ActualOmegaTower OrdinalRealizationTargets OrdinalNativeIterationTargets
open OrdinalNativeOrbitProof OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets
open scoped Ordinal

theorem countable_val_lt (c : CountableOrdinal) : c.val < ω₁ :=
  (OrdinalCountablePrefixOmegaProof.exact_CountablePrefixIffBelowOmegaOne c.val).1 c.property

noncomputable def mkCountable (x : Ordinal.{0}) (h : x < ω₁) : CountableOrdinal :=
  ⟨x, (OrdinalCountablePrefixOmegaProof.exact_CountablePrefixIffBelowOmegaOne x).2 h⟩

theorem bddAbove_orbit (A : FiniteType) (g : CountableOrdinal → CountableOrdinal) {ι : Type*} (F : ι → CountableOrdinal) :
    BddAbove (Set.range (fun i => (F i).val)) :=
  ⟨ω₁, fun _ ⟨i, hi⟩ => hi ▸ (countable_val_lt (F i)).le⟩

/-- At a limit stage the orbit lies above each earlier stage. -/
theorem orbit_le_limit (g : CountableOrdinal → CountableOrdinal) (x : CountableOrdinal)
    (lim : CountableOrdinal) (hlim : Order.IsSuccLimit lim.val) (β : CountableOrdinal) (hβ : β.val < lim.val) :
    (orbit .base g x β).val ≤ (orbit .base g x lim).val := by
  have sup : (orbit .base g x lim).val =
      ⨆ e : EarlierStages lim, (orbit .base g x (earlierStage lim e)).val :=
    (orbitEquations .base g x).2.2 lim hlim
  rw [sup]
  have e : earlierStage lim ⟨β.val, hβ⟩ = β := Subtype.ext rfl
  have := le_ciSup (bddAbove_orbit .base g (fun e : EarlierStages lim => orbit .base g x (earlierStage lim e)))
    ⟨β.val, hβ⟩
  rw [e] at this
  exact this

section
variable (N : CountableOrdinal → CountableOrdinal) (Γ : CountableOrdinal)

theorem orbit_strictMono (hN : Inflationary N) :
    ∀ α β : CountableOrdinal, α.val < β.val → (orbit .base N Γ α).val < (orbit .base N Γ β).val := by
  have eqs := orbitEquations .base N Γ
  have claim : ∀ b : Ordinal.{0}, ∀ β : CountableOrdinal, β.val = b → ∀ α : CountableOrdinal,
      α.val < b → (orbit .base N Γ α).val < (orbit .base N Γ β).val := by
    intro b
    refine Ordinal.induction (p := fun b => ∀ β : CountableOrdinal, β.val = b → ∀ α : CountableOrdinal,
      α.val < b → (orbit .base N Γ α).val < (orbit .base N Γ β).val) b (fun b ih => ?_)
    intro β hβ α hα
    rcases zero_or_succ_or_isSuccLimit b with h0 | ⟨c, hc⟩ | hlim
    · subst h0
      exact (not_lt_zero hα).elim
    · have hcb : c < b := by rw [← hc]; exact Order.lt_succ c
      let γ := mkCountable c (hcb.trans (hβ ▸ countable_val_lt β))
      have step : orbit .base N Γ β = N (orbit .base N Γ γ) :=
        eqs.2.1 γ β (by rw [hβ, ← hc, Ordinal.add_one_eq_succ]; rfl)
      have hγ : (orbit .base N Γ γ).val < (orbit .base N Γ β).val := by rw [step]; exact hN _
      have hαc : α.val ≤ c := by
        rw [← hc] at hα
        exact Order.lt_succ_iff.1 hα
      rcases hαc.lt_or_eq with hlt | heq
      · exact (ih c hcb γ rfl α hlt).trans hγ
      · have : α = γ := Subtype.ext heq
        rw [this]
        exact hγ
    · have hsucc : α.val + 1 < b := hlim.add_one_lt hα
      let δ := mkCountable (α.val + 1) (hsucc.trans (hβ ▸ countable_val_lt β))
      have h1 : (orbit .base N Γ α).val < (orbit .base N Γ δ).val :=
        ih (α.val + 1) hsucc δ rfl α (Order.lt_add_one_iff.2 le_rfl)
      have h2 : (orbit .base N Γ δ).val ≤ (orbit .base N Γ β).val :=
        orbit_le_limit N Γ β (hβ ▸ hlim) δ (hβ ▸ hsucc)
      exact h1.trans_le h2
  intro α β h
  exact claim β.val β rfl α h

theorem orbit_mono (hN : Inflationary N) {α β : CountableOrdinal} (h : α.val ≤ β.val) :
    (orbit .base N Γ α).val ≤ (orbit .base N Γ β).val := by
  rcases h.lt_or_eq with h | h
  · exact (orbit_strictMono N Γ hN α β h).le
  · have : α = β := Subtype.ext h
    rw [this]

theorem orbit_id_le (hN : Inflationary N) : ∀ α : CountableOrdinal, α.val ≤ (orbit .base N Γ α).val := by
  have claim : ∀ a : Ordinal.{0}, ∀ α : CountableOrdinal, α.val = a → α.val ≤ (orbit .base N Γ α).val := by
    intro a
    refine Ordinal.induction (p := fun a => ∀ α : CountableOrdinal, α.val = a → α.val ≤ (orbit .base N Γ α).val)
      a (fun a ih => ?_)
    intro α hα
    by_contra hlt
    rw [not_le] at hlt
    let β := orbit .base N Γ α
    have hb := ih β.val (hα ▸ hlt) β rfl
    have := orbit_strictMono N Γ hN β α hlt
    exact absurd (hb.trans_lt this) (lt_irrefl _)
  intro α
  exact claim α.val α rfl

theorem orbit_zero (α : CountableOrdinal) (h : α.val = 0) : orbit .base N Γ α = Γ :=
  (orbitEquations .base N Γ).1 α h

end

theorem criticalFacts : CriticalFacts := by
  intro N Γ hN hΓ
  have zero : ∀ α : CountableOrdinal, Γ.val ≤ (orbit .base N Γ α).val := by
    intro α
    let z := mkCountable 0 zero_lt_omegaOne
    have hz : orbit .base N Γ z = Γ := orbit_zero N Γ z rfl
    have := orbit_mono N Γ hN (α := z) (β := α) (show (0 : Ordinal.{0}) ≤ α.val from not_lt.mp not_lt_zero)
    rwa [hz] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro θ ⟨α, rfl⟩
    exact hΓ.trans_le (zero α)
  · rintro θ ⟨α, rfl⟩
    exact countable_val_lt _
  · intro β hβ
    let α := mkCountable (β + 1) ((isSuccLimit_omega 1).add_one_lt hβ)
    refine ⟨_, ⟨α, rfl⟩, ?_⟩
    exact (Order.lt_add_one_iff.2 le_rfl).trans_le (orbit_id_le N Γ hN α)
  · intro f hf crit θ hθ
    choose α hα using crit
    have αmono : StrictMono (fun n => (α n).val) := by
      intro n m hnm
      by_contra hle
      rw [not_lt] at hle
      have := orbit_mono N Γ hN hle
      rw [hα, hα] at this
      exact absurd (hf hnm) (not_lt.2 this)
    have bdd : BddAbove (Set.range (fun n => (α n).val)) := Ordinal.bddAbove_range _
    let lam := ⨆ n, (α n).val
    have lamLt : lam < ω₁ := Ordinal.iSup_lt_omega_one (fun n => countable_val_lt (α n))
    let L := mkCountable lam lamLt
    have below : ∀ n, (α n).val ≤ lam := fun n => le_ciSup bdd n
    have limit : Order.IsSuccLimit lam := by
      rcases zero_or_succ_or_isSuccLimit lam with h0 | ⟨c, hc⟩ | hl
      · exfalso
        have := (αmono (Nat.lt_succ_self 0)).trans_le (below 1)
        rw [h0] at this
        exact not_lt_zero this
      · exfalso
        have hcl : c < lam := by rw [← hc]; exact Order.lt_succ c
        obtain ⟨n, hn⟩ := (lt_ciSup_iff bdd).1 hcl
        have h1 : lam ≤ (α n).val := by rw [← hc]; exact Order.succ_le_of_lt hn
        exact absurd ((h1.trans_lt (αmono (Nat.lt_succ_self n))).trans_le (below (n+1))) (lt_irrefl _)
      · exact hl
    refine ⟨L, le_antisymm ?_ ?_⟩
    · have sup : (orbit .base N Γ L).val =
          ⨆ e : EarlierStages L, (orbit .base N Γ (earlierStage L e)).val :=
        (orbitEquations .base N Γ).2.2 L limit
      rw [sup]
      refine ciSup_le' (fun e => ?_)
      obtain ⟨n, hn⟩ := (lt_ciSup_iff bdd).1 e.property
      have := orbit_strictMono N Γ hN (earlierStage L e) (α n) hn
      rw [hα] at this
      exact this.le.trans (hθ.1 ⟨n, rfl⟩)
    · refine hθ.2 (fun _ ⟨n, hn⟩ => ?_)
      rw [← hn, ← hα]
      exact orbit_mono N Γ hN (below n)

theorem veblenInflationary : VeblenInflationary := by
  intro Z s add mul w one pow fix h1 h2
  have infl : Inflationary (veblenValue fix pow) := by
    intro ζ
    have unfold : veblenValue fix pow ζ =
        fix (fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue) ζ :=
      congrFun (NativeTowerProof.towerValue_one fix (towerValue fix 0) (fix pow)) ζ
    let g : CountableOrdinal → CountableOrdinal :=
      fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue
    have fixEq : fix g ζ = orbit .base g (s ζ) w := h2.2.2.2.2 g ζ
    have wlim : Order.IsSuccLimit w.val := by rw [h2.1]; exact isSuccLimit_omega0
    let z := mkCountable 0 zero_lt_omegaOne
    have hz : orbit .base g (s ζ) z = s ζ := (orbitEquations .base g (s ζ)).1 z rfl
    have hzw : z.val < w.val := by rw [h2.1]; exact omega0_pos
    have le := orbit_le_limit g (s ζ) w wlim z hzw
    rw [hz] at le
    rw [unfold]
    change ζ.val < (fix g ζ).val
    rw [fixEq]
    refine lt_of_lt_of_le ?_ le
    rw [h1.2.1 ζ]
    exact Order.lt_add_one_iff.2 le_rfl
  refine ⟨infl, ?_⟩
  have hw : (1 : Ordinal.{0}) < w.val := by rw [h2.1]; exact one_lt_omega0
  exact hw.trans (infl w)

end LogicLineages.PersistentMarking.ActualCollapse
