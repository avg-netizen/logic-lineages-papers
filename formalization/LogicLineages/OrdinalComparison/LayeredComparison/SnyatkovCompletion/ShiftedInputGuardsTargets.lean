module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsTargets
open NormalForm ShiftedInputGuards

def ActualAtomicComparisons : Prop :=
  (∀ (a b : Input) (ν : Nat → Nat), (less a b).eval ν ↔ value a ν < value b ν) ∧
  (∀ (a : Input) (c : Nat) (ν : Nat → Nat), (bound c a).eval ν ↔ c ≤ value a ν)

def ActualGuardCompilation : Prop := ∀ (xs : List Input)
    (p : CommonHeadLargeGuards.Formula) (ν : Nat → Nat),
  (compile xs p).eval ν ↔ p.eval (valuation xs ν)

def LiteralGuardLinearity : Prop := ∀ (xs : List Input)
    (p : CommonHeadLargeGuards.Formula) (i : Nat),
  LinearRows.isLinear i (compile xs p) = true

def OriginalInputCalibration : Prop := ∀ (r : Row) (ν : Nat → Nat),
  CommonHeadLargeGuards.inputRow (coefficients r) (valuation (inputs r) ν) =
    PlainPhiDominance.phiData r ν

def ActualCancellationGuard : Prop := ∀ (r : Row) (ν : Nat → Nat),
  (canceled r).eval ν ↔ CommonHeadCollectedRow.collect (PlainPhiDominance.phiData r ν) = []

def ActualBlockGuard : Prop := ∀ (r : Row) (k : Nat) (desired : Int) (ν : Nat → Nat),
  (block r k desired).eval ν ↔ Int.sign
    (CommonHeadCollectedRow.coefficient (PlainPhiDominance.phiData r ν)
      (valuation (inputs r) ν k)) = desired

/-- A finite Boolean guard over original raw names selects the actual sign in
the active maximal-name branch. No independent head values or chosen surviving
leader are supplied to this statement. -/
def ActualFiniteActiveBranch : Prop := ∀ (r : Row), PlainPhiDominance.isPlain r = true →
  ∀ (i : Nat) (ν : Nat → Nat), PlainPhiDominance.threshold r ≤ ν i →
    (∀ a ∈ r.2, ν a.2.name ≤ ν i) → PlainPhiDominance.active i r ν = true →
    ∀ desired : Int, (activeSign r desired).eval ν ↔ Int.sign (rowValue r ν) = desired

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsTargets
