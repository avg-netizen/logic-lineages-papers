module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowTargets

def ActualNonlinearLinearBound : Prop :=
  ∀ (kind : Bool) (e h : Int) (a n : Nat),
    (LinearWindow.valueTerm 0 kind e h).value (fun _ => n) ≤ a * n →
      n < LinearWindow.bound kind e h a

/-- SourceII3/II4 guard, with BOTH original variables and their actual nonlinear
occurrences: the linear variable has a concrete finite bound. -/
def ActualGuardBound : Prop :=
  ∀ (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) (ν : Nat → Nat),
    (LinearWindow.guard i j leftKind rightKind e h k l a).eval ν →
      ν j < LinearWindow.bound rightKind k l a

def ActualFiniteElimination : Prop :=
  ∀ (i j : Nat), i ≠ j → ∀ (leftKind rightKind : Bool) (e h k l : Int)
    (a : Nat) (p : Matrix) (ν : Nat → Nat),
    (∃ n : Nat, (LinearWindow.guard i j leftKind rightKind e h k l a).eval
      (Function.update ν j n) ∧ p.eval (Function.update ν j n)) ↔
      (LinearWindow.finiteCases i j leftKind rightKind e h k l a p).eval ν

def ExactSupportReduction : Prop :=
  ∀ (i j : Nat), i ≠ j → ∀ (leftKind rightKind : Bool) (e h k l : Int)
    (a : Nat) (p : Matrix) (v : Nat),
    v ∈ (LinearWindow.finiteCases i j leftKind rightKind e h k l a p).variables →
      v ≠ j ∧ (v = i ∨ v ∈ p.variables)

def ActualBoundProgram : Prop :=
  Primrec (fun p : Bool × (Int × (Int × Nat)) =>
    LinearWindow.bound p.1 p.2.1 p.2.2.1 p.2.2.2)

def LiteralCodeCalibration : Prop :=
  ∀ (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) (p : Matrix),
    LinearWindow.Code.finiteCases (LinearWindow.Code.input i j leftKind rightKind e h k l a p.encode) =
      (LinearWindow.finiteCases i j leftKind rightKind e h k l a p).encode

def ActualCodeComputation : Prop := Computable LinearWindow.Code.finiteCases

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowTargets
