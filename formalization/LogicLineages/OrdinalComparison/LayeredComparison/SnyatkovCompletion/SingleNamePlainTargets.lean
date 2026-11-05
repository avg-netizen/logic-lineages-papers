module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainTargets
open NormalForm SingleNamePlain

def ExactFragmentTest : Prop := ∀ (i : Nat) (p : Formula),
  admissible i p = true ↔ MaximalPlainBranch.isPlain p = true ∧ ∀ j ∈ p.variables, j = i

def ActualExistentialElimination : Prop := ∀ (i : Nat) (p : Formula), admissible i p = true →
  ∀ ν : Nat → Nat, (existsEliminate i p).eval ν ↔ ∃ n : Nat, p.eval (Function.update ν i n)

def ActualUniversalElimination : Prop := ∀ (i : Nat) (p : Formula), admissible i p = true →
  ∀ ν : Nat → Nat, (forallEliminate i p).eval ν ↔ ∀ n : Nat, p.eval (Function.update ν i n)

def ExactRemovedName : Prop := ∀ (i : Nat) (p : Formula),
  i ∉ (existsEliminate i p).variables ∧ i ∉ (forallEliminate i p).variables

def LiteralCodeCalibration : Prop := ∀ (i : Nat) (p : Formula),
  Code.admissible i p.encode = admissible i p ∧
  Code.existsEliminate i p.encode = (existsEliminate i p).encode ∧
  Code.forallEliminate i p.encode = (forallEliminate i p).encode

def ActualNumericPrograms : Prop :=
  Primrec₂ Code.admissible ∧ Primrec₂ Code.existsEliminate ∧ Primrec₂ Code.forallEliminate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainTargets
