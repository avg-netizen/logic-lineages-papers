module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsTargets
open NormalForm FiniteBranchRows

/-- The existing genuine source guard implies the finite bound. Names may coincide. -/
def ActualLinearBranchElimination : Prop :=
  ∀ (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) (p : Formula) (ν : Nat → Nat),
    (linearCases i j leftKind rightKind e h k l a p).eval ν ↔
      ∃ n : Nat, (LinearWindow.guard i j leftKind rightKind e h k l a).eval
        (Function.update ν j n) ∧ p.eval (Function.update ν j n)
def ActualActiveHyperBranchElimination : Prop :=
  ∀ (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Formula) (ν : Nat → Nat),
    (activeCases i j kind e h k l q a p).eval ν ↔
      ∃ n : Nat, (ActiveHyper.guard i j kind e h k l q a).eval
        (Function.update ν j n) ∧ p.eval (Function.update ν j n)
def ExactBranchSupport : Prop :=
  (∀ (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) (p : Formula) (v : Nat),
    v ∈ (linearCases i j leftKind rightKind e h k l a p).variables ↔
      v ≠ j ∧ (v = i ∨ v ∈ p.variables)) ∧
  (∀ (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Formula) (v : Nat),
    v ∈ (activeCases i j kind e h k l q a p).variables ↔
      v ≠ j ∧ (v = i ∨ v ∈ p.variables))
def LiteralBranchCodeCalibration : Prop :=
  (∀ (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) (p : Formula),
    Code.linearCases (LinearWindow.Code.input i j leftKind rightKind e h k l a p.encode) =
      (linearCases i j leftKind rightKind e h k l a p).encode) ∧
  (∀ (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Formula),
    Code.activeCases (ActiveHyper.Code.input i j kind e h k l q a p.encode) =
      (activeCases i j kind e h k l q a p).encode)
def ActualBranchNumericPrograms : Prop := Primrec Code.linearCases ∧ Primrec Code.activeCases

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsTargets
