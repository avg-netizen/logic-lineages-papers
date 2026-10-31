module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChainDefinitions
public import Mathlib.Algebra.Group.Subgroup.Ker
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

def reservoirComplement (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (i : ℕ) : AddSubgroup (ReservoirGroup A B C) where
  carrier := {x | x.1=0 ∧ (∀ n : ℕ, n<i → x.2.1 n=0) ∧ x.2.2=0}
  zero_mem' := ⟨rfl,fun _ _ => rfl,rfl⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨?_,?_,?_⟩
    · change x.1+y.1=0; rw [hx.1,hy.1,zero_add]
    · intro n hn; change x.2.1 n+y.2.1 n=0; rw [hx.2.1 n hn,hy.2.1 n hn,zero_add]
    · change x.2.2+y.2.2=0; rw [hx.2.2,hy.2.2,zero_add]
  neg_mem' := by
    intro x hx
    refine ⟨?_,?_,?_⟩
    · change -x.1=0; rw [hx.1,neg_zero]
    · intro n hn; change -x.2.1 n=0; rw [hx.2.1 n hn,neg_zero]
    · change -x.2.2=0; rw [hx.2.2,neg_zero]
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
