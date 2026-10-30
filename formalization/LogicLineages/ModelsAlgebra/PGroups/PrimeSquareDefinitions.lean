module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Literal cyclic inclusion induced by multiplication by p on integer
representatives. Its periodicity is the standard p*p=0 in ZMod(p^2). -/
noncomputable def primeSquareInclusion (p : ℕ) : ZMod p →+ ZMod (p ^ 2) :=
  ZMod.lift p (A := ZMod (p ^ 2)) ⟨(nsmulAddMonoidHom p : ZMod (p ^ 2) →+ ZMod (p ^ 2)).comp (Int.castAddHom (ZMod (p ^ 2))), by
    change p • ((p : ℤ) : ZMod (p ^ 2)) = 0
    rw [Int.cast_natCast, nsmul_eq_mul, ← Nat.cast_mul, ← pow_two]
    exact ZMod.natCast_self (p ^ 2)⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
