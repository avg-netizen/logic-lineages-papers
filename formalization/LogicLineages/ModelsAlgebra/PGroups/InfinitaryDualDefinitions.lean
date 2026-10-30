module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions

@[expose] public section

/-! Explicit dual normal forms for the paper01 Sigma/Pi convention.
No frozen syntax is changed. Quantifier blocks and branch sets are preserved;
existential/disjunction and universal/conjunction swap, and QF leaves are
negated. Syntactic involution is NOT asserted: a QF double dual has two negations. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

def Polarity.opposite : Polarity → Polarity
  | .sigma => .pi
  | .pi => .sigma

def Formula.dual : {n : ℕ} → Formula n → Formula n
  | _, .qf q => .qf (.neg q)
  | _, .disjEx s m matrix => .conjAll s m (fun i => (matrix i).dual)
  | _, .conjAll s m matrix => .disjEx s m (fun i => (matrix i).dual)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
