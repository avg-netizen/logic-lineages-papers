module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsTargets
open NormalForm PlainWindowRows

def ActualGuardCalibration : Prop := ∀ (i j : Nat) (e k : Int) (c : Nat) (ν : Nat → Nat),
  ((plusGuard i j e k c).eval ν ↔
    (closeMatrix i (shiftTerm (.variable j) k) e c).eval ν ∧
      (shiftDomain (.variable j) k).eval ν) ∧
  ((minusGuard i j e k c).eval ν ↔
    (ReverseWindow.closeMatrix i (shiftTerm (.variable j) k) e c).eval ν ∧
      (shiftDomain (.variable j) k).eval ν)
/-- Literal source replacements, including both nested truncation defaults. -/
def ActualCandidateSubstitution : Prop := ∀ (i j : Nat) (e k : Int) (d : Nat)
    (p : Formula) (ν : Nat → Nat),
  ((plusSubstitute i j e k d p).eval ν ↔
    p.eval (Function.update ν i ((replacementTerm (shiftTerm (.variable j) k) e d).value ν))) ∧
  ((minusSubstitute i j e k d p).eval ν ↔
    p.eval (Function.update ν i
      ((ReverseWindow.replacementTerm (shiftTerm (.variable j) k) e d).value ν)))
/-- The original anchor domain is explicit in the compared source body. -/
def ActualBranchCalibration : Prop := ∀ (i j : Nat) (e k : Int) (c : Nat)
    (p : Formula) (ν : Nat → Nat),
  ((plusCases i j e k c p).eval ν ↔
    (finiteWindow i (shiftTerm (.variable j) k) e c
      (.conjunction (shiftDomain (.variable j) k) p.compile)).eval ν) ∧
  ((minusCases i j e k c p).eval ν ↔
    (ReverseWindow.finiteCases i (shiftTerm (.variable j) k) e c
      (.conjunction (shiftDomain (.variable j) k) p.compile)).eval ν)
def ActualFiniteElimination : Prop := ∀ (i j : Nat), i ≠ j →
  ∀ (e k : Int) (c : Nat) (p : Formula) (ν : Nat → Nat),
    ((∃ n : Nat, (closeMatrix i (shiftTerm (.variable j) k) e c).eval (Function.update ν i n) ∧
      (shiftDomain (.variable j) k).eval (Function.update ν i n) ∧
      p.eval (Function.update ν i n)) ↔ (plusCases i j e k c p).eval ν) ∧
    ((∃ n : Nat, (ReverseWindow.closeMatrix i (shiftTerm (.variable j) k) e c).eval
        (Function.update ν i n) ∧ (shiftDomain (.variable j) k).eval (Function.update ν i n) ∧
      p.eval (Function.update ν i n)) ↔ (minusCases i j e k c p).eval ν)
def ExactBranchSupport : Prop := ∀ (i j : Nat), i ≠ j →
  ∀ (e k : Int) (c : Nat) (p : Formula) (v : Nat),
    (v ∈ (plusCases i j e k c p).variables ↔ v ≠ i ∧ (v = j ∨ v ∈ p.variables)) ∧
    (v ∈ (minusCases i j e k c p).variables ↔ v ≠ i ∧ (v = j ∨ v ∈ p.variables))
def LiteralBranchCodeCalibration : Prop := ∀ (i j : Nat) (e k : Int) (c : Nat) (p : Formula),
  Code.plusCases (Code.input i j e k c p.encode) = (plusCases i j e k c p).encode ∧
  Code.minusCases (Code.input i j e k c p.encode) = (minusCases i j e k c p).encode
def ActualBranchNumericPrograms : Prop := Primrec Code.plusCases ∧ Primrec Code.minusCases

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsTargets
