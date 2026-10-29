module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

/-!
# Actual multiplication-by-p subgroup images

This semantic module contains no project proof candidate. The finite
filtration is the finite part of the source's transfinite p-filtration,
starting at the whole actual additive group.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

variable {G : Type*} [AddCommGroup G]

def pStep (p : ℕ) (S : AddSubgroup G) : AddSubgroup G :=
  S.map (nsmulAddMonoidHom p)

def finiteFiltration (p : ℕ) : ℕ → AddSubgroup G
  | 0 => ⊤
  | n + 1 => pStep p (finiteFiltration p n)

end LogicLineages.ModelsAlgebra.PGroups
