module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelsTargets

@[expose] public section

/-! # The level diagonal at limits, every level

Frozen before proof (local Fable-trio round, 27 November 2026, root lane). The third conjunct of
`ActualCalibrationLevels.LevelFactsAt l`, for every `l` and every pair `fix`, `pow` (no equations
needed): it is the limit clause of the full-prefix orbit, read through the spine. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationLevels
open Ordinal OrdinalRealizationTargets OrdinalNativeOrbitProof OrdinalNativeIterationTargets
open NativeTowerTargets NativeTowerSequenceTargets

def LevelDiagonalLimit : Prop :=
  ∀ (fix : Value (tier 2)) (pow : Value (tier 1)) (l : Nat) (lim : CountableOrdinal),
    Order.IsSuccLimit lim.val →
    (levelDiagonal fix pow l lim).val =
      ⨆ e : EarlierStages lim, (levelDiagonal fix pow l (earlierStage lim e)).val

end LogicLineages.PersistentMarking.ActualCalibrationLevels
