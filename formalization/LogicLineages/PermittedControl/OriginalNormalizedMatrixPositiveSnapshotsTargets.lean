module
public import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
open OriginalPrintedCircuitNormalization (NormalizedGate Holds)
open OriginalNormalizedCircuitMatrix (rowsList passingList)
open HeterogeneousSignedMatrixSlice (Snapshot actualRows)

def AllTrue (s : Snapshot) : Prop := ∀ v ∈ s, v.2 = true

def ExactPositiveCircuitSnapshots : Prop :=
  ∀ (f θ : Nat → Nat) (gs : List NormalizedGate) (snap : Snapshot),
    (actualRows f θ (rowsList gs) snap ∧ AllTrue snap) ↔
      Holds f θ gs ∧ snap = passingList θ gs

end LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
