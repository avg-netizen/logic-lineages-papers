module
public import LogicLineages.OrdinalComparison.ActualUnaryRayDefinitions
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitDefinitions
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction
open ForwardTranslation Arithmetic

noncomputable def shiftedHead (a : ClosedPositive) (δ : Nat) : Ordinal :=
  fixedHead a + Ordinal.omega0 * (δ : Ordinal)
noncomputable def threshold (a : ClosedPositive) (c δ : Nat) : Nat :=
  max (actualOrdinalNorm (shiftedHead a δ)) (ActualUnaryRay.totalNorm a c 0)

/-- Every genuine point below the exact threshold, and no nongenuine point.
These are mathematical constant evaluations; numeric encoding is separate. -/
noncomputable def finitePrefix (a : ClosedPositive) (c δ : Nat) (t y : Expr) : Formula :=
  disjunction (((List.range (threshold a c δ)).filter
    (fun j => decide (actualOrdinalNorm (shiftedHead a δ) ≤ j))).map fun j =>
      .and (.eq t (.numeral j)) (.eq y (.numeral (actualHeadValue (shiftedHead a δ) j))))

/-- The raw z input is natural, so its actual source scalar z_0 is z+1.
All ray range constraints are inside this tail branch. The fixed number δ
of Phi gates uses the existing actual S formulas, not an iteration atom. -/
noncomputable def tail {Γ : List Ty} (q : UnitElimination.Tree Nat (.ground::Γ))
    (a : ClosedPositive) (c δ : Nat) (t y : Expr) : Formula :=
  .and (.le (.numeral (threshold a c δ)) t)
    (.existsNat (.existsNat (conjunction [
      phiChain δ (t.lift 2) (.add (.numeral (ActualUnaryRay.totalNorm a c 0)) (.variable 1)),
      unitFormula q (.variable 1 :: List.replicate Γ.length (.numeral 0)) (.variable 0),
      .eq (y.lift 2) (.add (.variable 0) (.numeral δ)) ])))

noncomputable def graph {Γ : List Ty} (q : UnitElimination.Tree Nat (.ground::Γ))
    (a : ClosedPositive) (c δ : Nat) (t y : Expr) : Formula :=
  .or (finitePrefix a c δ t y) (tail q a c δ t y)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction
