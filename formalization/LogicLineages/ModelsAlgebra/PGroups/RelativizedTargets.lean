module
public import LogicLineages.ModelsAlgebra.PGroups.RelativizedDefinitions
public import Mathlib.Algebra.Group.Subgroup.Lattice
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupRelativizedTopAgreement : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (φ : Formula n) (a : Fin n → G),
    φ.RealizeIn (⊤ : AddSubgroup G) a ↔ φ.Realize a

def groupRelativizedSubgroupAgreement : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (S : AddSubgroup G) (n : ℕ) (φ : Formula n) (a : Fin n → S),
    φ.RealizeIn S (fun j => (a j : G)) ↔ φ.Realize a

end LogicLineages.ModelsAlgebra.PGroups.Targets
