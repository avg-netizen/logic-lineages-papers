module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowStandardInduction
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.GorbowStandardInductionProof

open GorbowSyntax GorbowStandardInstances GorbowStandardInduction

theorem successorSemantics : Comparators.GorbowStandardInduction.SuccessorSemantics := by
  intro n φ I v x
  let σ : Fin (n + 1) → Term (n + 1) :=
    Fin.cases (.succ (.var 0)) (fun i : Fin n => .var i.succ)
  have h := GorbowFormulaSubstitution.substituteFormula_realize φ I (Fin.cases x v) σ
  have he : (fun i => (σ i).realize I (Fin.cases x v)) = Fin.cases (x + 1) v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he] at h
  exact h

theorem baseSemantics : Comparators.GorbowStandardInduction.BaseSemantics := by
  intro n φ I v
  exact GorbowStandardInstancesProof.literalInstantiation n φ .zero I v

theorem openInductionRealized : Comparators.GorbowStandardInduction.OpenInductionRealized := by
  intro n φ I v hb hs x
  induction x with
  | zero => exact (baseSemantics n φ I v).mp hb
  | succ x ih => exact (successorSemantics n φ I v x).mp (hs x ih)

theorem universalClosureSemantics : Comparators.GorbowStandardInduction.UniversalClosureSemantics := by
  intro n
  induction n with
  | zero =>
    intro φ I
    constructor
    · intro h v
      have he : v = Fin.elim0 := by funext i; exact Fin.elim0 i
      rw [he]
      exact h
    · intro h
      exact h Fin.elim0
  | succ n ih =>
    intro φ I
    change (universalClosure (Formula.all φ)).realize I Fin.elim0 ↔ _
    rw [ih]
    constructor
    · intro h v
      have he : Fin.cases (v 0) (fun i : Fin n => v i.succ) = v := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hv := h (fun i : Fin n => v i.succ) (v 0)
      rw [he] at hv
      exact hv
    · intro h v x
      exact h (Fin.cases x v)

theorem closedInductionRealized : Comparators.GorbowStandardInduction.ClosedInductionRealized := by
  intro n φ I
  exact (universalClosureSemantics n (inductionAxiom φ) I).mpr
    (openInductionRealized n φ I)

theorem gorbowStandardInduction : Comparators.GorbowStandardInduction.Target :=
  ⟨successorSemantics, baseSemantics, openInductionRealized,
    universalClosureSemantics, closedInductionRealized⟩

end LogicLineages.ComputabilityKnowledge.GorbowStandardInductionProof
