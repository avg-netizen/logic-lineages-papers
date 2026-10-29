module

public import LogicLineages.ModelsAlgebra.PGroups.FiltrationDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

/-!
# The source's actual transfinite p-filtration

The ordinal recursion starts at the whole group, takes actual
multiplication-by-p images at successors, and intersects all earlier
subgroups at nonzero limits. No filtration law, monotonicity or quotient
compatibility theorem is a field in an assumed interface.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

universe u v

variable {G : Type u} [AddCommGroup G]

noncomputable def transfiniteFiltration (p : ℕ) (α : Ordinal.{v}) : AddSubgroup G :=
  Ordinal.limitRecOn α ⊤ (fun _ S => pStep p S)
    (fun β _ ih => ⨅ γ : Set.Iio β, ih γ.1 γ.2)

end LogicLineages.ModelsAlgebra.PGroups
