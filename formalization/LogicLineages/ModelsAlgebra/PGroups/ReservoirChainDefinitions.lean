module
public import LogicLineages.ModelsAlgebra.PGroups.FreshCombineDefinitions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

abbrev ReservoirGroup (A B C : Type) [Zero B] [Zero C] := A × ((ℕ →₀ B) × (ℕ →₀ C))

def reservoirStage (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (i : ℕ) : AddSubgroup (ReservoirGroup A B C) where
  carrier := {x | ∀ n : ℕ, i ≤ n → x.2.1 n = 0}
  zero_mem' := by intro n _; rfl
  add_mem' := by
    intro x y hx hy n hn
    change x.2.1 n + y.2.1 n = 0
    rw [hx n hn, hy n hn, zero_add]
  neg_mem' := by
    intro x hx n hn
    change -(x.2.1 n) = 0
    rw [hx n hn, neg_zero]

noncomputable def reservoirStageMap (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (i M : ℕ) (j : B →+ C) : ReservoirGroup A B C →+ reservoirStage A B C i := by
  let low : ReservoirGroup A B C →+ (ℕ →₀ B) :=
    (AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _)
  let high : ReservoirGroup A B C →+ (ℕ →₀ C) :=
    (AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _)
  let lowPrefix := (Finsupp.filterAddHom (fun n : ℕ => n < i)).comp low
  let tail := (Finsupp.filterAddHom (fun n : ℕ => i ≤ n)).comp low
  let f : ReservoirGroup A B C →+ ReservoirGroup A B C :=
    (AddMonoidHom.fst _ _).prod (lowPrefix.prod ((freshCombine B C M j).comp (tail.prod high)))
  exact f.codRestrict (reservoirStage A B C i) (by
    intro x n hn
    change (if n < i then x.2.1 n else 0) = 0
    exact if_neg (not_lt_of_ge hn))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
