module
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Module.NatInt
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

def integerMultipleHom (G : Type u) [AddCommGroup G] (x : G) : ℤ →+ G where
  toFun z := z • x
  map_zero' := zero_zsmul x
  map_add' a b := add_zsmul x a b

def adjunctionHom (G : Type u) [AddCommGroup G] (B : AddSubgroup G) (x : G) : B × ℤ →+ G :=
  B.subtype.comp (AddMonoidHom.fst B ℤ) +
    (integerMultipleHom G x).comp (AddMonoidHom.snd B ℤ)

def mappedAdjunctionHom (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (B : AddSubgroup G) (f : B →+ H) (w : H) : B × ℤ →+ H :=
  f.comp (AddMonoidHom.fst B ℤ) +
    (integerMultipleHom H w).comp (AddMonoidHom.snd B ℤ)

end LogicLineages.ModelsAlgebra.PGroups
