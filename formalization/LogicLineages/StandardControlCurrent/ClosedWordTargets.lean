module
public import LogicLineages.StandardControlCurrent.ClosedWordDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ClosedWordTargets
open OrdinalComparison WordLinearDecisionCompletion ClosedWord

def BoundCalibration : Prop :=
  (∀ bs p, withBoundsCode bs (Formula.encode p) = Formula.encode (withBounds bs p)) ∧
  (∀ bs p ν, Formula.meaningful (withBounds bs p) ν ↔ Formula.meaningful p ν) ∧
  (∀ bs p ν, Formula.eval ν (withBounds bs p) ↔ BoundsHold bs ν ∧ Formula.eval ν p) ∧
  (∀ D bs p, Formula.allowed D (withBounds bs p) ↔ Formula.allowed D p)

def Programs : Prop :=
  Primrec (fun x : Bounds × Nat => withBoundsCode x.1 x.2) ∧
  Computable (fun x : Nat × Bounds × Nat => solve x.1 x.2.1 x.2.2)

def GeneralizedDecision : Prop :=
  ∀ D bs p, Formula.allowed D p →
    (solve D bs (Formula.encode p) = true ↔
      ∃ ν : Nat → Nat, BoundsHold bs ν ∧ Formula.meaningful p ν ∧ Formula.eval ν p)

/-- Literal printed source domain: bounds alone, once they genuinely pay
all original occurrence domains independently of Boolean truth. -/
def SourceDecision : Prop :=
  ∀ D bs p, 3 ≤ D → Formula.allowed D p → Adequate bs p →
    (solve D bs (Formula.encode p) = true ↔
      ∃ ν : Nat → Nat, BoundsHold bs ν ∧ Formula.eval ν p)

def FullClosedExistential : Prop :=
  BoundCalibration ∧ Programs ∧ GeneralizedDecision ∧ SourceDecision
end LogicLineages.StandardControlCurrent.ClosedWordTargets
