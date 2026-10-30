module

public import LogicLineages.ModelsAlgebra.Forests.LeafClusterDefinitions
public import Mathlib.Data.Fintype.Prod

/-! Explicit finite subdivision relation for paper03 positive-width templates.
Each original vertex is replaced by a chain of n points. Correctness, foresthood,
and leaf counts are not assumed by this raw relation. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

def thickLE (T : FiniteOrderForest) (n : Nat) (x y : T.Carrier × Fin n) : Prop :=
  x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 ≤ y.2)

end LogicLineages.ModelsAlgebra.Forests
