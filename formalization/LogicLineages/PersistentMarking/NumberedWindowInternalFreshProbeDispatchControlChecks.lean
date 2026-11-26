module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlTargets
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchControlTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

private theorem literalSame (n k : Nat) :
    literal n k = InternalFixedWindowVertexDispatch.constant n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Program.composition .succ (fun _ : Fin 1 => literal n k) =
      Program.composition .succ (fun _ : Fin 1 => InternalFixedWindowVertexDispatch.constant n k)
    rw [ih]

theorem exact_DispatchControlAST : ExactDispatchControlAST :=
  ⟨fun _ => rfl,literalSame,rfl,rfl,fun _ _ _ _ => rfl,fun _ _ _ => rfl⟩

theorem exact_DispatchObjectTypeCode : ExactDispatchObjectTypeCode := by
  intro τ
  induction τ with
  | ground => rfl
  | arrow σ τ ihσ ihτ =>
    simp only [NumberedWindowProbeCode.code,NumberedWindowInternalProbeTargets.typeCode,ihσ,ihτ]

#print axioms exact_DispatchControlAST
#print axioms exact_DispatchObjectTypeCode
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
