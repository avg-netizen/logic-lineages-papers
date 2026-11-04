module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeTargets

/-- The THREE emitted literal codes are exactly the sourceII6 finite-left,
finite-right and equal-index matrices. Every original domain/comparison and
the original arbitrary matrix is retained; no semantic code-field premise. -/
def LiteralCalibration : Prop :=
  ∀ (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix),
    let data := HyperWindowCode.input i j e h k l c p.encode
    HyperWindowCode.leftCases data = (HyperWindow.leftCases i j e h k l c p).encode ∧
    HyperWindowCode.rightCases data = (HyperWindow.rightCases i j e h k l c p).encode ∧
    HyperWindowCode.equalCases data = (HyperWindow.equalCases i j e h k l c p).encode

/-- Total numerical effectivity on EVERY input code, including invalid matrix
codes. Semantic calibration is separately stated for actual source matrices. -/
def ActualCodeComputation : Prop :=
  Computable HyperWindowCode.leftCases ∧ Computable HyperWindowCode.rightCases ∧
    Computable HyperWindowCode.equalCases

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeTargets
