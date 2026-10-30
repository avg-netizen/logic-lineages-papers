module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.NatInt

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Literal integer multiples modulo the actual annihilator bound. Modulus
zero retains ZMod 0=integers; only positive prime powers are used for injection. -/
noncomputable def cyclicRootHom (n : ℕ) (G : Type) [AddCommGroup G] (y : G) (hy : n • y = 0) :
    ZMod n →+ G :=
  ZMod.lift n (A := G) ⟨
    { toFun := fun a : ℤ => a • y
      map_zero' := zero_zsmul y
      map_add' := fun a b => add_zsmul y a b },
    by
      change (n : ℤ) • y = 0
      simpa only [natCast_zsmul] using hy⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
