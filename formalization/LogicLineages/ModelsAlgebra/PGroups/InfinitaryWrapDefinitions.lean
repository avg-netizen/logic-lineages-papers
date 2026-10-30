module

public import LogicLineages.ModelsAlgebra.PGroups.CountableBranchesDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Literal singleton existential wrapper with zero new variables. -/
noncomputable def sigmaWrap {n : ℕ} (φ : Formula n) : Formula n :=
  countableDisjEx (fun _ : Unit => 0) (fun _ => φ)

/-- Literal singleton universal wrapper with zero new variables. -/
noncomputable def piWrap {n : ℕ} (φ : Formula n) : Formula n :=
  countableConjAll (fun _ : Unit => 0) (fun _ => φ)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
