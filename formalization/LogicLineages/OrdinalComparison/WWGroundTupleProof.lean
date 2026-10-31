module
public import LogicLineages.OrdinalComparison.WWGroundTupleTargets
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open SourceTypedPorts

theorem groundPositiveTupleComplete : Targets.GroundPositiveTupleComplete := by
  intro Γ
  induction Γ with
  | nil =>
    intro _ ρ hp
    refine ⟨[], rfl, ?_⟩
    rintro ⟨σ, x, j⟩
    cases x
  | cons σ Γ ih =>
    intro hΓ ρ hp
    have hσ : σ = Ty.ground := hΓ σ (by simp)
    subst σ
    let tailρ : OrdinalComponent Γ → Nat := fun c => ρ ⟨c.1, .there c.2.1, c.2.2⟩
    have htail : ∀ σ ∈ Γ, σ = Ty.ground := fun σ h => hΓ σ (by simp [h])
    obtain ⟨xs, hlen, hx⟩ := ih htail tailρ (fun c => hp _)
    refine ⟨(ρ ⟨Ty.ground, .here, 0⟩ - 1) :: xs, by simp [hlen], ?_⟩
    rintro ⟨τ, x, j⟩
    cases x with
    | here =>
      have hj : j = 0 := by
        apply Fin.ext
        have h := j.isLt
        change j.val < 1 at h
        change j.val = 0
        omega
      subst j
      have hpos := hp ⟨Ty.ground, .here, 0⟩
      simp only [variableIndex, List.getD_cons_zero]
      omega
    | there x =>
      simpa only [variableIndex, List.getD_cons_succ] using hx ⟨τ, x, j⟩

theorem groundTuplePositive : Targets.GroundTuplePositive := by
  intro Γ xs c
  exact Nat.zero_lt_succ _

theorem emptyContextTupleUnique : Targets.EmptyContextTupleUnique := by
  intro xs
  exact List.length_eq_zero_iff
end LogicLineages.OrdinalComparison.Source
