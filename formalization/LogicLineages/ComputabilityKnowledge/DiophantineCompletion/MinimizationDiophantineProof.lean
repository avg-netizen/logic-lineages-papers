module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationSemanticProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Proof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BoundedUniversalProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationDiophantineProof
open Dioph MinimizationTargets RowPackingClosureProof

private theorem graphOnFunctions {α : Type} (c : Nat.Partrec.Code)
    (hc : Dioph (graph (Nat.Partrec.Code.eval c)))
    (f g : (α → Nat) → Nat) (hf : DiophFn f) (hg : DiophFn g) :
    Dioph {v | g v ∈ Nat.Partrec.Code.eval c (f v)} := by
  exact finCompose hc ![f,g] (by
    intro i
    fin_cases i
    · exact hf
    · exact hg)

private theorem nonzeroOnFunction {α : Type} (c : Nat.Partrec.Code)
    (hc : Dioph (graph (Nat.Partrec.Code.eval c)))
    (f : (α → Nat) → Nat) (hf : DiophFn f) :
    Dioph {v | ∃ z : Nat, z ∈ Nat.Partrec.Code.eval c (f v) ∧ z ≠ 0} := by
  have hg := graphOnFunctions c hc (fun v : Option α → Nat => f (v ∘ some))
    (fun v => v none) (Dioph.reindex_diophFn some hf) (Dioph.proj_dioph none)
  have hn := Dioph.ne_dioph (Dioph.proj_dioph (none : Option α)) (Dioph.const_dioph 0)
  exact Dioph.ex1_dioph (hg.inter hn)

theorem shiftedSearchDiophantine : ShiftedSearchDiophantine := by
  intro c hc
  let R : Nat → (Fin 3 → Nat) → Prop := fun i v =>
    ∃ z : Nat, z ∈ Nat.Partrec.Code.eval c (Nat.pair (v 0) (i + v 1)) ∧ z ≠ 0
  have hR : Dioph {w : Option (Fin 3) → Nat | R (w none) (w ∘ some)} :=
    nonzeroOnFunction c hc (fun w => Nat.pair (w (some 0)) (w none + w (some 1)))
      (Proof.pairDiophantine _ _ _ (Dioph.proj_dioph (some 0))
        (Dioph.add_dioph (Dioph.proj_dioph none) (Dioph.proj_dioph (some 1))))
  have hAll := BoundedUniversalProof.variableBoundedUniversalClosure 3
    (fun v => v 2) R (Dioph.proj_dioph 2) hR
  have hZero := graphOnFunctions c hc
    (fun v : Fin 3 → Nat => Nat.pair (v 0) (v 2 + v 1)) (fun _ => 0)
    (Proof.pairDiophantine _ _ _ (Dioph.proj_dioph 0)
      (Dioph.add_dioph (Dioph.proj_dioph 2) (Dioph.proj_dioph 1))) (Dioph.const_dioph 0)
  exact hZero.inter hAll

theorem ordinaryRfindGraphClosure : OrdinaryRfindGraphClosure := by
  intro c hc
  let A : (Option (Fin 2) → Nat) → Nat := fun v => (Nat.unpair (v (some 0))).1
  let M : (Option (Fin 2) → Nat) → Nat := fun v => (Nat.unpair (v (some 0))).2
  let T : (Option (Fin 2) → Nat) → Nat := fun v => v none
  have hAM := Proof.unpairDiophantine _ (fun v : Option (Fin 2) → Nat => v (some 0))
    (Dioph.proj_dioph (some 0))
  have hT : DiophFn T := Dioph.proj_dioph none
  have hSearch := finCompose (shiftedSearchDiophantine c hc) ![A,M,T] (by
    intro i
    fin_cases i
    · exact hAM.1
    · exact hAM.2
    · exact hT)
  have hEq := Dioph.eq_dioph (Dioph.proj_dioph (some (1 : Fin 2)))
    (Dioph.add_dioph hT hAM.2)
  apply (Dioph.ex1_dioph (hEq.inter hSearch)).ext
  intro v
  change (∃ t : Nat, v 1 = t + (Nat.unpair (v 0)).2 ∧
    0 ∈ Nat.Partrec.Code.eval c (Nat.pair (Nat.unpair (v 0)).1 (t + (Nat.unpair (v 0)).2)) ∧
    ∀ i, i < t → ∃ z : Nat,
      z ∈ Nat.Partrec.Code.eval c (Nat.pair (Nat.unpair (v 0)).1 (i + (Nat.unpair (v 0)).2)) ∧ z ≠ 0) ↔
    v 1 ∈ Nat.Partrec.Code.eval (.rfind' c) (v 0)
  simpa only [Nat.pair_unpair] using
    (MinimizationSemanticProof.ordinaryRfindSpecification c
      (Nat.unpair (v 0)).1 (Nat.unpair (v 0)).2 (v 1)).symm

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationDiophantineProof
