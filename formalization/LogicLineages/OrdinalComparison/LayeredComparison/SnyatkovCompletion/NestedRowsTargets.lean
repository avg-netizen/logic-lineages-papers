module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsTargets
open NormalForm NestedRows

/-- Total all-valuation semantics, with no domain or distinct-name premise. -/
def ActualNestedSubstitution : Prop := ∀ (i j : Nat) (a b : Int) (p : Formula) (ν : Nat → Nat),
  (substitute i j a b p).eval ν ↔ p.eval (Function.update ν i (replacement j a b ν))
def ExactNestedSupport : Prop := ∀ (i j : Nat) (a b : Int) (p : Formula) (v : Nat),
  v ∈ (substitute i j a b p).variables ↔ v = j ∨ (v ≠ i ∧ v ∈ p.variables)
def ActualGuardedAtomSubstitution : Prop := ∀ (i j : Nat) (a b : Int) (atom : Atom) (ν : Nat → Nat),
  (substitute i j a b (guardedAtom atom)).eval ν ↔
    rowMeaningful atom.row (Function.update ν i (replacement j a b ν)) ∧
      atom.eval (Function.update ν i (replacement j a b ν))
def LiteralCodeCalibration : Prop := ∀ (i j : Nat) (a b : Int) (p : Formula),
  Code.substitute i j a b p.encode = (substitute i j a b p).encode
def ActualNumericPrograms : Prop :=
  Primrec₂ (fun args : Code.Input => Code.substitute args.1.1 args.1.2 args.2.1 args.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsTargets
