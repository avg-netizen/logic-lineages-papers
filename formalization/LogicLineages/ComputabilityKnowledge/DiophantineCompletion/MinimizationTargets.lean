module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationTargets

/-- The original Mathlib rfind' returns an absolute index. Every earlier
offset has a defined nonzero value; undefined computations are not skipped. -/
def OrdinaryRfindSpecification : Prop :=
  ∀ (c : Nat.Partrec.Code) (a start y : Nat),
    y ∈ Nat.Partrec.Code.eval (.rfind' c) (Nat.pair a start) ↔
      ∃ t : Nat, y = t + start ∧
        0 ∈ Nat.Partrec.Code.eval c (Nat.pair a (t + start)) ∧
        ∀ i, i < t → ∃ z : Nat,
          z ∈ Nat.Partrec.Code.eval c (Nat.pair a (i + start)) ∧ z ≠ 0

/-- The first-zero relation on actual evaluated code, with free parameter,
starting index, and search offset. The interval is genuinely variable. -/
def ShiftedSearchDiophantine : Prop :=
  ∀ (c : Nat.Partrec.Code), Dioph (graph (Nat.Partrec.Code.eval c)) →
    Dioph {v : Fin 3 → Nat |
      0 ∈ Nat.Partrec.Code.eval c (Nat.pair (v 0) (v 2 + v 1)) ∧
      ∀ i, i < v 2 → ∃ z : Nat,
        z ∈ Nat.Partrec.Code.eval c (Nat.pair (v 0) (i + v 1)) ∧ z ≠ 0}

/-- Closure for the actual unchanged ordinary code constructor. This does
not assume primitive recursion, a universal evaluator, or MRDP. -/
def OrdinaryRfindGraphClosure : Prop :=
  ∀ (c : Nat.Partrec.Code), Dioph (graph (Nat.Partrec.Code.eval c)) →
    Dioph (graph (Nat.Partrec.Code.eval (.rfind' c)))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationTargets
