module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperTargets

def ActualCoefficientCollisionBound : Prop :=
  ∀ (e h k : Int) (a n : Nat),
    SnyatkovHyperCollision.translatedValue (((n : Int) + e).toNat) h ≤
      a * Phi (((n : Int) + k).toNat) → n < ActiveHyper.bound e h k a

def ActualGuardBound : Prop :=
  ∀ (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (ν : Nat → Nat),
    (ActiveHyper.guard i j kind e h k l q a).eval ν → ν j < ActiveHyper.bound k l q a

/-- Complete finite alternative before a potentially nested-H substitution.
Both names and repeated/dependent occurrences share the original ν, even i=j. -/
def ActualFiniteElimination : Prop :=
  ∀ (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Matrix) (ν : Nat → Nat),
    (∃ n : Nat, (ActiveHyper.guard i j kind e h k l q a).eval (Function.update ν j n) ∧
      p.eval (Function.update ν j n)) ↔
      (ActiveHyper.finiteCases i j kind e h k l q a p).eval ν

def ExactSupportReduction : Prop :=
  ∀ (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Matrix) (v : Nat),
    v ∈ (ActiveHyper.finiteCases i j kind e h k l q a p).variables →
      v ≠ j ∧ (v = i ∨ v ∈ p.variables)

def ActualBoundProgram : Prop :=
  Primrec (fun p : Int × (Int × (Int × Nat)) => ActiveHyper.bound p.1 p.2.1 p.2.2.1 p.2.2.2)

def LiteralCodeCalibration : Prop :=
  ∀ (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Matrix),
    ActiveHyper.Code.finiteCases (ActiveHyper.Code.input i j kind e h k l q a p.encode) =
      (ActiveHyper.finiteCases i j kind e h k l q a p).encode

def ActualCodeComputation : Prop := Computable ActiveHyper.Code.finiteCases

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperTargets
