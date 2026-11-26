module
public import LogicLineages.PermittedControl.OriginalFieldGateMatrixTargets
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalFieldGateInfiniteStrip
open OriginalNaturalFieldGates (Gate Valuation)
open HeterogeneousSignedMatrixSlice (Row Snapshot HitRows actualRows sliceRows)
open HeterogeneousSignedMatrixLowStrips (branches)
open OriginalFieldGateMatrix (rowsList passingList)

/-- Only the selected coordinate is updated. Every other coordinate
is determined by the arbitrary, not bounded, original valuation. -/
def ExactFieldGateInfiniteStrips : Prop :=
  ∀ (f ρ : Valuation) (rank bound : Nat) (gates : List Gate) (testRows : List Row)
    (prior : Valuation → Prop) (test : Valuation → Snapshot → Prop) (positive : Bool),
    (∃ a : Nat, a < bound ∧
      let θ := Function.update ρ rank a
      prior θ ∧ (∀ gate ∈ gates, gate.graph f θ) ∧
        ∃ testValues : Snapshot, actualRows f θ testRows testValues ∧
          (if positive then test θ testValues else ¬ test θ testValues)) ↔
    ∃ branch residual,
      branch ∈ branches f rank bound (rowsList gates ++ testRows) ∧ HitRows branch.2 residual ∧
      let θ := Function.update ρ rank branch.1
      prior θ ∧ ∃ testValues : Snapshot,
        actualRows f θ residual (passingList θ gates ++ testValues) ∧
          (if positive then test θ testValues else ¬ test θ testValues)

/-- No occurrence of any unselected rank moves or disappears when slicing
succeeds. Both original list order and multiplicity remain literal. -/
def ExactFieldGateResidualOperands : Prop :=
  ∀ (f : Valuation) (rank a : Nat) (gates : List Gate) (testRows residual : List Row),
    HitRows (sliceRows f rank a (rowsList gates ++ testRows)) residual →
    residual.map Prod.fst = (rowsList gates ++ testRows).map Prod.fst ∧
    residual.map (fun r => r.2.2) =
      (rowsList gates ++ testRows).map (fun r => SignedRowCoordinateSlice.untouched rank r.2.2)

def FullOriginalFieldGateInfiniteStrip : Prop :=
  ExactFieldGateInfiniteStrips ∧ ExactFieldGateResidualOperands

end LogicLineages.PermittedControl.OriginalFieldGateInfiniteStrip
