module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingTargets
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingClosureProof
open Dioph

private theorem listForall {α β : Type} (R : β → Set (α → Nat))
    (hR : ∀ b, Dioph (R b)) (L : List β) : Dioph {v | ∀ b ∈ L, v ∈ R b} := by
  induction L with
  | nil =>
      exact (Dioph.eq_dioph (Dioph.const_dioph (0 : Nat)) (Dioph.const_dioph 0)).ext (fun v => by simp)
  | cons b L ih => exact ((hR b).inter ih).ext (fun v => by simp)

theorem finiteForall {α β : Type} [Fintype β] (R : β → Set (α → Nat))
    (hR : ∀ b, Dioph (R b)) : Dioph {v | ∀ b, v ∈ R b} := by
  classical
  exact (listForall R hR Finset.univ.toList).ext (fun v => by simp)

/-- Transport the existing finite-vector composition theorem to ordinary Fin
coordinates. This is fixed finite composition, not bounded universal closure. -/
theorem finCompose {α : Type} {m : Nat} {S : Set (Fin m → Nat)} (hS : Dioph S)
    (f : Fin m → (α → Nat) → Nat) (hf : ∀ i, DiophFn (f i)) :
    Dioph {v | (fun i => f i v) ∈ S} := by
  let e := Fin2.equivFin m
  have hr := Dioph.reindex_dioph (Fin2 m) e.symm hS
  have h := Dioph.dioph_comp hr (fun i => f (e i))
    ((vectorAllP_iff_forall _ _).2 (fun i => hf (e i)))
  apply h.ext
  intro v
  change (fun i => f (e (e.symm i)) v) ∈ S ↔ (fun i => f i v) ∈ S
  simp only [Equiv.apply_symm_apply]

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingClosureProof
