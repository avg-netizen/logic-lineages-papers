module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersProof
open CommonLayerSyntax ScopedPhiParameters

theorem additiveTermOutput : ScopedPhiParametersTargets.AdditiveTermOutput := by
  intro ambient t
  induction t <;> simp_all [freezeTerm, AdditiveSource.termTest]

theorem additiveFormulaOutput : ScopedPhiParametersTargets.AdditiveFormulaOutput := by
  intro ambient p
  induction p <;> simp_all [freezeFormula, AdditiveSource.test, additiveTermOutput ambient]

theorem phi_test (bound : List Nat) (t : BaseTerm) : termTest bound (.phi t) = true ↔
    ∀ i ∈ t.variables, i ∉ bound := by
  simp [termTest, List.all_eq_true]

theorem scopedTermMeaning : ScopedPhiParametersTargets.ScopedTermMeaning := by
  intro bound ambient current t ht hagree
  induction t generalizing bound current with
  | numeral n => rfl
  | «variable» i => rfl
  | add a b iha ihb =>
      have hh := Bool.and_eq_true_iff.mp ht
      exact congrArg₂ Nat.add (iha bound current hh.1 hagree) (ihb bound current hh.2 hagree)
  | phi t ih =>
      have hf := (phi_test bound t).mp ht
      change (BaseTerm.phi t).value ambient = (BaseTerm.phi t).value current
      symm
      apply BaseTermPrograms.Proof.supportStability
      intro i hi
      exact hagree i (hf i hi)

theorem literalScopeBoundary : ScopedPhiParametersTargets.LiteralScopeBoundary := by
  refine ⟨phi_test, ?_, ?_⟩
  · intro bound i p; rfl
  · intro i
    simp [test, termTest, BaseTerm.variables]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersProof
