module
public import LogicLineages.ModelsAlgebra.PGroups.FreshCoordinatesDefinitions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Group.Prod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

noncomputable def freshCombine (B C : Type) [AddCommGroup B] [AddCommGroup C]
    (M : ℕ) (j : B →+ C) : ((ℕ →₀ B) × (ℕ →₀ C)) →+ (ℕ →₀ C) :=
  ((Finsupp.mapDomain.addMonoidHom (reserveOdd M)).comp (Finsupp.mapRange.addMonoidHom j)).comp
    (AddMonoidHom.fst _ _) +
    (Finsupp.mapDomain.addMonoidHom (reserveEven M)).comp (AddMonoidHom.snd _ _)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
