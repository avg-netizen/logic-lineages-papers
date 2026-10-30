module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocleCoordinatesDefinitions
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.Finsupp.ToDFinsupp
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

abbrev CyclicRootSum (p N : ℕ) (I : Fin N → Type) :=
  Π₀ a : (Σ l : Fin N, I l), ZMod (p ^ (a.1.val+1))

noncomputable def cyclicRootSumHom (p N : ℕ) (I : Fin N → Type) (G : Type) [AddCommGroup G]
    (y : ∀ l : Fin N, I l → G) (hy : ∀ l i, p ^ (l.val+1) • y l i = 0) :
    CyclicRootSum p N I →+ G := by
  classical
  exact DFinsupp.sumAddHom (fun a => cyclicRootHom (p ^ (a.1.val+1)) G (y a.1 a.2) (hy a.1 a.2))

noncomputable def cyclicSocleCoefficients (p : ℕ) [Fact p.Prime] (N : ℕ) (I : Fin N → Type) :
    ((Σ l : Fin N, I l) →₀ ZMod p) →+ CyclicRootSum p N I where
  toFun c := DFinsupp.mapRange (fun a => cyclicSocleCoordinate p a.1.val)
    (fun a => map_zero (cyclicSocleCoordinate p a.1.val)) c.toDFinsupp
  map_zero' := by ext a; exact map_zero (cyclicSocleCoordinate p a.1.val)
  map_add' := by intro c d; ext a; exact map_add (cyclicSocleCoordinate p a.1.val) (c a) (d a)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
