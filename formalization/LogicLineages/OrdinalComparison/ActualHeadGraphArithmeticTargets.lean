module
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic.Targets

/-- Every small input and every nonnegative S-input; no eventual-only gate. -/
def FullPhiGate : Prop := ∀ (a b : Expr) (ν : Nat → Nat),
  (phi a b).eval ν ↔ b.value ν = Phi (a.value ν)

/-- A literal fixed finite number of actual S/Phi gates, not an iteration
oracle or a premise supplying the desired graph. -/
def FixedPhiChain : Prop := ∀ (d : Nat) (a b : Expr) (ν : Nat → Nat),
  (phiChain d a b).eval ν ↔ b.value ν = (Phi^[d]) (a.value ν)

/-- Exact expansion of the checked unit-elimination syntax. All source atoms
are actual ground sources; original names share their positional input wire.
The tuple length guards against deleting a slot absent from malformed data. -/
def UnitTreeExpansion : Prop := ∀ (Γ : List Ty) (q : UnitElimination.Tree Nat Γ)
    (xs : List Expr), Γ.length ≤ xs.length → ∀ (r : Expr) (ν : Nat → Nat),
  (unitFormula q xs r).eval ν ↔ UnitElimination.Eval q (inputValues ν xs) (r.value ν)

end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic.Targets
