module
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.HeterogeneousSignedMatrixSlice

theorem exactGuardedMatrixTests : ExactGuardedMatrixTests := by
  intro f ρ rank a rows agree test positive
  constructor
  · rintro ⟨values,actual,holds⟩
    obtain ⟨residual,hits,residualActual⟩ := (exactMatrixSnapshots f ρ rank a rows agree values).mp actual
    exact ⟨residual,values,hits,residualActual,holds⟩
  · rintro ⟨residual,values,hits,residualActual,holds⟩
    exact ⟨values,(exactMatrixSnapshots f ρ rank a rows agree values).mpr ⟨residual,hits,residualActual⟩,holds⟩

end LogicLineages.PermittedControl.HeterogeneousSignedMatrixSlice
