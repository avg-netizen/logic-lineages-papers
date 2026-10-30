module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTuple
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryTuple
open GorbowSyntax GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowRegistryTuple

def PairInjection : Prop := ∀ a b c d, pair a b = pair c d ↔ a=c ∧ b=d

def TupleInjection : Prop := Function.Injective tuple

def HeaderInjection : Prop := ∀ arity tag args arity' tag' args',
  header arity tag args = header arity' tag' args' ↔ arity=arity' ∧ tag=tag' ∧ args=args'

def Bounds : Prop := (∀ a b, a≤pair a b ∧ b≤pair a b) ∧ (∀ a as, tuple as < tuple (a::as))

def ArithmeticConstructors : Prop :=
  (∀ n (a b : Term n), ArithmeticTerm a → ArithmeticTerm b → ArithmeticTerm (pairTerm a b)) ∧
  (∀ n (as : List (Term n)), (∀ t ∈ as, ArithmeticTerm t) → ArithmeticTerm (tupleTerm as)) ∧
  (∀ n arity tag (as : List (Term n)), (∀ t ∈ as, ArithmeticTerm t) → ArithmeticTerm (headerTerm arity tag as))

def TermCalibration : Prop := ∀ n (I : Interpretation) (v : Fin n → Nat),
  (∀ a b : Term n, (pairTerm a b).realize I v = pair (a.realize I v) (b.realize I v)) ∧
  (∀ as : List (Term n), (tupleTerm as).realize I v = tuple (as.map (fun t => t.realize I v))) ∧
  (∀ arity tag (as : List (Term n)), (headerTerm arity tag as).realize I v = header arity tag (as.map (fun t => t.realize I v)))

def UniformPrograms : Prop := Primrec (fun p : Nat × Nat => pair p.1 p.2) ∧ Primrec tuple ∧
  Primrec (fun p : Nat × Nat × List Nat => header p.1 p.2.1 p.2.2)

def Target : Prop := PairInjection ∧ TupleInjection ∧ HeaderInjection ∧ Bounds ∧ ArithmeticConstructors ∧ TermCalibration ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryTuple
