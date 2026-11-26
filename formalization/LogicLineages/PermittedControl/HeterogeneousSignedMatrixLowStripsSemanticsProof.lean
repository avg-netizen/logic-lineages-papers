module
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsTargets
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStrips
open HeterogeneousSignedMatrixSlice (sliceRows)
open StatementChecks (fixed_heterogeneousSignedMatrixSnapshots)

theorem exactBranch : ExactBranch := by
  intro f rank bound rows branch
  rw [branches,List.mem_map]
  constructor
  · rintro ⟨a,within,rfl⟩
    exact ⟨List.mem_range.mp within,rfl⟩
  · rintro ⟨within,shape⟩
    exact ⟨branch.1,List.mem_range.mpr within,Prod.ext rfl shape.symm⟩

theorem exactGuardedLowExistential : ExactGuardedLowExistential := by
  intro f ρ prior rank bound rows test positive
  constructor
  · rintro ⟨a,within,guard,values,actual,holds⟩
    have agree : Function.update ρ rank a rank = a := Function.update_self _ _ _
    obtain ⟨residual,hits,residualActual⟩ :=
      (fixed_heterogeneousSignedMatrixSnapshots f (Function.update ρ rank a) rank a rows agree values).mp actual
    refine ⟨(a,sliceRows f rank a rows),residual,?_,hits,guard,values,residualActual,holds⟩
    exact (exactBranch f rank bound rows _).mpr ⟨within,rfl⟩
  · rintro ⟨branch,residual,member,hits,guard,values,actual,holds⟩
    obtain ⟨within,shape⟩ := (exactBranch f rank bound rows branch).mp member
    rw [shape] at hits
    have agree : Function.update ρ rank branch.1 rank = branch.1 := Function.update_self _ _ _
    have sourceActual :=
      (fixed_heterogeneousSignedMatrixSnapshots f (Function.update ρ rank branch.1)
        rank branch.1 rows agree values).mpr ⟨residual,hits,actual⟩
    exact ⟨branch.1,within,guard,values,sourceActual,holds⟩

end LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStrips
