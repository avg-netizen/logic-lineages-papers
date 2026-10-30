module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteMultiplicityTargets
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Logic.Equiv.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem finite_multiplicity_enumeration : Targets.groupFiniteMultiplicityEnumeration := by
  classical
  intro n m
  let X := Σ j : Fin n, Fin (m j)
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let ell : Fin (Fintype.card X) → ℕ := fun a => (e.symm a).1.val+1
  refine ⟨Fintype.card X,ell,?_,?_⟩
  · intro a
    have h := (e.symm a).1.isLt
    constructor <;> dsimp [ell] <;> omega
  · intro j
    let q : {a : Fin (Fintype.card X) // ell a = j.val+1} ≃ {x : X // x.1 = j} :=
      Equiv.subtypeEquiv e.symm (by
        intro a
        change (e.symm a).1.val+1 = j.val+1 ↔ (e.symm a).1 = j
        simp only [Nat.add_right_cancel_iff, Fin.val_inj])
    calc
      Nat.card {a : Fin (Fintype.card X) // ell a = j.val+1} = Nat.card (Fin (m j)) :=
        Nat.card_congr (q.trans (Equiv.sigmaSubtype j))
      _ = m j := Nat.card_fin _

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
