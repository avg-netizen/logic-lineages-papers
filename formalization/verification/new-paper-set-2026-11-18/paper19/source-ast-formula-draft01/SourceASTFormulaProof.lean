module
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaBudgetProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceAST
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source

theorem concrete : SourceASTFormulaTargets.Concrete := by
  intro p f Γ ρ a
  have hc : a.toInput.eval p f ρ Fin.elim0 ↔ a.eval p f ρ=true :=
    formula_semantic p f a (fun x => x) ρ ρ (fun _ => rfl) Fin.elim0
      (fun _ _ root => .finish root) (fun b => b=true) (by
        intro Ξ n s e μ w hs he root
        rfl)
  refine ⟨hc,?_⟩
  exact (InputNormalization.normalization p f Γ ρ 0 .nil a.toInput).trans hc

theorem concreteBudgets : SourceASTFormulaTargets.ConcreteBudgets := by
  intro Γ a
  have h := formula_budgets a (fun x => x) (m:=0) (fun _ _ root => .finish root) 1 0 (by
    intro Ξ n s e root
    exact ⟨Nat.le_refl 1,Nat.le_refl 0⟩)
  have hh := InputNormalization.budgets Γ 0 .nil a.toInput
  have hs : a.toProgram.codeSize ≤ a.cost+1 := by
    change (InputNormalization.normalize .nil a.toInput).codeSize ≤ _
    rw [hh.1]
    simpa [Formula.toInput] using h.1
  have hm : a.toProgram.sourceMax ≤ a.sourceMax := by
    change (InputNormalization.normalize .nil a.toInput).sourceMax ≤ _
    rw [hh.2.1]
    simpa [Formula.toInput] using h.2
  refine ⟨hs,hm,?_⟩
  exact (InputNormalization.program_load_le a.toProgram).trans
    (Nat.mul_le_mul hs (Nat.add_le_add_right hm 1))

theorem prefix : SourceASTFormulaTargets.Prefix := by
  intro p f s
  constructor
  · rintro ⟨ρ,hρ⟩
    exact ⟨ρ,(concrete p f _ ρ s.matrix).2.mpr hρ⟩
  · rintro ⟨ρ,hρ⟩
    exact ⟨ρ,(concrete p f _ ρ s.matrix).2.mp hρ⟩
end LogicLineages.ControlSensitivityCurrent.SourceAST
