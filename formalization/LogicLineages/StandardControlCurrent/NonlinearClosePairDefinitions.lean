module
public import LogicLineages.StandardControlCurrent.InverseCutSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NonlinearClosePair
open OrdinalComparison LayeredComparison.SnyatkovCompletion

def guard (x k C : Nat) (v : Term) : Matrix :=
  .conjunction (InverseCutSyntax.le (.phi v) (.phi (.add (.variable x) (.numeral k))))
    (.less (.phi (.add (.variable x) (.numeral k))) (.multiply C (.phi v)))
def candidate (v : Term) (k j : Nat) : Term := .subtract (.add v (.numeral j)) (.numeral k)
def branch (x k C : Nat) (v : Term) (p : Matrix) (j : Nat) : Matrix :=
  .conjunction (InverseCutSyntax.le (.numeral k) (.add v (.numeral j)))
    ((Matrix.conjunction (guard x k C v) p).substitute x (candidate v k j))
def compile (x k C : Nat) (v : Term) (p : Matrix) : Matrix :=
  Matrix.any ((List.range (C+1)).map (branch x k C v p))
def Quantified (x k C : Nat) (v : Term) (p : Matrix) (ν : Nat → Nat) : Prop :=
  ∃ n : Nat, (Matrix.conjunction (guard x k C v) p).eval (Function.update ν x n)

def guardCode (x k C v : Nat) : Nat :=
  WindowCode.conjunction
    (WindowCode.atMost (WindowCode.phi v) (WindowCode.phi (WindowCode.add (WindowCode.var x) (WindowCode.numeral k))))
    (WindowCode.less (WindowCode.phi (WindowCode.add (WindowCode.var x) (WindowCode.numeral k)))
      (WindowCode.multiply C (WindowCode.phi v)))
def candidateCode (v k j : Nat) : Nat :=
  WindowCode.subtract (WindowCode.add v (WindowCode.numeral j)) (WindowCode.numeral k)
def branchCode (x k C v p j : Nat) : Nat :=
  WindowCode.conjunction (WindowCode.atMost (WindowCode.numeral k) (WindowCode.add v (WindowCode.numeral j)))
    (WindowCode.matrixSubstitute x (candidateCode v k j) (WindowCode.conjunction (guardCode x k C v) p))
abbrev Input := Nat × Nat × Nat × Nat × Nat
def program (q : Input) : Nat :=
  WindowCode.any ((List.range (q.2.2.1+1)).map (branchCode q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
end LogicLineages.StandardControlCurrent.NonlinearClosePair
