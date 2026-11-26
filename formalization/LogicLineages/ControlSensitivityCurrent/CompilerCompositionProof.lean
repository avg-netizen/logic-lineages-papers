module
public import LogicLineages.ControlSensitivityCurrent.CompilerCompositionTargets
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaProof
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CompilerComposition
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan

theorem astCorrect : CompilerCompositionTargets.ASTCorrect := by
  intro f hf p s
  have h := PolicyProgramComparison.comparison f hf p _ s.matrix.toProgram
  have he := not_congr (SourceAST.prefixCoverage p f s)
  exact ⟨h.1.trans he.symm,h.2.trans he.symm⟩

theorem normalize_nil (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (q : InputNormalization.Input Γ 0) (ρ : Variable Γ .ground → Nat) :
    InputNormalization.programEval p f ρ (InputNormalization.normalize .nil q) ↔
      q.eval p f ρ Fin.elim0 := by
  exact InputNormalization.normalization p f Γ ρ 0 .nil q

theorem sharedCorrect : CompilerCompositionTargets.SharedCorrect := by
  intro f hf p n q
  have h := PolicyProgramComparison.comparison f hf p _ (InputNormalization.normalize .nil q)
  have he := not_congr (exists_congr (normalize_nil p f q))
  exact ⟨h.1.trans he,h.2.trans he⟩

theorem ground_context {Γ} (hg : ∀ σ ∈ Γ, σ = Ty.ground) (q : BooleanCompiler.Program Γ) :
    ∀ σ ∈ (compile (BooleanCompiler.lower q)).context, σ = Ty.ground :=
  (PolicyPlan.actualSize Γ (BooleanCompiler.lower q)).2.2.2 hg

theorem retention : CompilerCompositionTargets.Retention := by
  intro f hf p n q ρ
  refine ⟨(normalize_nil p f q ρ).symm.trans
    ((PolicyProgram.forest f hf p _ (InputNormalization.normalize .nil q)).1 ρ),?_⟩
  apply ground_context
  intro σ hσ
  exact (List.mem_replicate.mp hσ).2

theorem outputBudgets : CompilerCompositionTargets.OutputBudgets := by
  constructor
  · intro s
    have hb := SourceAST.concreteBudgets _ s.matrix
    have hs := PolicyProgramComparison.outputSizes _ s.matrix.toProgram
    have hm : BooleanCompiler.budget s.matrix.toProgram ≤
        10000*(s.matrix.cost+1)*(s.matrix.sourceMax+1)+7 := by
      unfold BooleanCompiler.budget
      have h1 := Nat.mul_le_mul_left 10000 hb.1
      have h2 := Nat.mul_le_mul h1 (Nat.add_le_add_right hb.2.1 1)
      exact Nat.add_le_add_right h2 7
    refine ⟨ground_context (fun σ hσ => by exact (List.mem_replicate.mp hσ).2) s.matrix.toProgram,
      hs.1.trans hm,hs.2.1.trans hm,hs.2.2.1.trans hm,hs.2.2.2.trans hm⟩
  · intro n q
    have hb := InputNormalization.budgets _ 0 .nil q
    have hs := PolicyProgramComparison.outputSizes _ (InputNormalization.normalize .nil q)
    have he : BooleanCompiler.budget (InputNormalization.normalize .nil q) =
        10000*q.cost*(q.sourceMax+1)+7 := by
      unfold BooleanCompiler.budget
      rw [hb.1,hb.2.1]
      simp
    rw [he] at hs
    exact ⟨ground_context (fun σ hσ => by exact (List.mem_replicate.mp hσ).2) _,hs⟩
end LogicLineages.ControlSensitivityCurrent.CompilerComposition
