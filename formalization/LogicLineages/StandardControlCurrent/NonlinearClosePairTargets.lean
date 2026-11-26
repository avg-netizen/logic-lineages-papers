module
public import LogicLineages.StandardControlCurrent.NonlinearClosePairDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NonlinearClosePairTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearClosePair

def ActualWidth : Prop := ∀ (C a b : Nat), Phi a ≤ Phi b → Phi b < C*Phi a →
  a ≤ b ∧ b < a+(C+1)
def SubstitutionSemantics : Prop :=
  (∀ (t r : Term) (x : Nat) (ν : Nat → Nat),
    (t.substitute x r).value ν = t.value (Function.update ν x (r.value ν))) ∧
  (∀ (p : Matrix) (r : Term) (x : Nat) (ν : Nat → Nat),
    (p.substitute x r).eval ν ↔ p.eval (Function.update ν x (r.value ν)))
def ParameterElimination : Prop := ∀ (x k C : Nat) (v : Term) (p : Matrix) (ν : Nat → Nat),
  x ∉ v.variables → ((compile x k C v p).eval ν ↔ Quantified x k C v p ν)
def Support : Prop := ∀ (x k C : Nat) (v : Term) (p : Matrix), x ∉ v.variables →
  ∀ i, i ∈ (compile x k C v p).variables → i ≠ x ∧ (i ∈ v.variables ∨ i ∈ p.variables)
def BoundaryCases : Prop := ∀ (x k : Nat) (v : Term) (p : Matrix) (ν : Nat → Nat),
  ¬ (compile x k 0 v p).eval ν ∧ ¬ (compile x k 1 v p).eval ν
def LiteralCode : Prop := ∀ (x k C : Nat) (v : Term) (p : Matrix),
  program (x,k,C,v.encode,p.encode) = (compile x k C v p).encode
def Programs : Prop :=
  Computable (fun q : Nat × Nat × Nat => WindowCode.termSubstitute q.1 q.2.1 q.2.2) ∧
  Computable (fun q : Nat × Nat × Nat => WindowCode.matrixSubstitute q.1 q.2.1 q.2.2) ∧
  Computable program

def Full : Prop := ActualWidth ∧ SubstitutionSemantics ∧ ParameterElimination ∧ Support ∧ BoundaryCases ∧ LiteralCode ∧ Programs
end LogicLineages.StandardControlCurrent.NonlinearClosePairTargets
