module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnitDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Targets
open CotreePresburgerLinear

def PeriodPositive : Prop := ∀ n (u : UnitFormula n), 0 < period u

def InstantiationExact : Prop :=
  ∀ n (u : UnitFormula n) (b : Affine n) (v : Fin n → Int),
    evalQF (instantiate u b) v = evalUnit u v (b.eval v)

/-- A genuine finite single-Nat-quantifier elimination theorem for arbitrary
Boolean combinations of unit-coefficient order/divisibility atoms. -/
def UnitEliminationExact : Prop :=
  ∀ n (u : UnitFormula n) (v : Fin n → Int),
    evalQF (eliminate u) v = true ↔ ∃ x : Nat, evalUnit u v (x : Int) = true

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Targets
