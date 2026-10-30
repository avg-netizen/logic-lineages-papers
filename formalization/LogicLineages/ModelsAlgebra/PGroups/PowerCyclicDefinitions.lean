module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Actual inclusion of cyclic p-power groups, induced by integer
multiplication by p^(k−ℓ); only genuine divisibility ℓ≤k is required. -/
noncomputable def powerCyclicInclusion (p ℓ k : ℕ) (h : ℓ ≤ k) :
    ZMod (p ^ ℓ) →+ ZMod (p ^ k) :=
  ZMod.lift (p ^ ℓ) (A := ZMod (p ^ k))
    ⟨(nsmulAddMonoidHom (p ^ (k - ℓ)) : ZMod (p ^ k) →+ ZMod (p ^ k)).comp
      (Int.castAddHom (ZMod (p ^ k))), by
      change p ^ (k - ℓ) • (((p ^ ℓ : ℕ) : ℤ) : ZMod (p ^ k)) = 0
      rw [Int.cast_natCast, nsmul_eq_mul, ← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel h]
      exact ZMod.natCast_self (p ^ k)⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
