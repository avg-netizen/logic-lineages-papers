module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeTargets

def LiteralCalibration : Prop :=
  (∀ (i : Nat) (r a : Term),
    WindowCode.termSubstitute i r.encode a.encode = (a.substitute i r).encode) ∧
  (∀ (i : Nat) (r : Term) (p : Matrix),
    WindowCode.matrixSubstitute i r.encode p.encode = (p.substitute i r).encode) ∧
  (∀ (i : Nat) (a : Term) (e : Int) (c : Nat) (p : Matrix),
    WindowCode.finiteWindow (i, a.encode, e, c, p.encode) =
      (finiteWindow i a e c p).encode)

def ActualCodeComputation : Prop :=
  Computable (fun p : Nat × (Nat × Nat) => WindowCode.termSubstitute p.2.1 p.2.2 p.1) ∧
  Computable (fun p : Nat × (Nat × Nat) => WindowCode.matrixSubstitute p.2.1 p.2.2 p.1) ∧
  Computable WindowCode.finiteWindow

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeTargets
