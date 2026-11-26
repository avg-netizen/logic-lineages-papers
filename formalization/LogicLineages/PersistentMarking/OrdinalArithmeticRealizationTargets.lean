module

public import LogicLineages.PersistentMarking.OrdinalOmegaOrbitTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalArithmeticRealizationTargets
open OrdinalRealizationTargets OrdinalNativeOrbitProof OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets

abbrev Base := FiniteType.base
abbrev OrdinalFunction := FiniteType.arrow Base Base
abbrev BinaryOrdinalFunction := FiniteType.arrow Base OrdinalFunction
abbrev FixedPointFunction := FiniteType.arrow OrdinalFunction OrdinalFunction
abbrev OrdinalIteratorType := FiniteType.arrow Base FixedPointFunction

structure ArithmeticTerms (terms : TermStructure) where
  iterator : terms.term OrdinalIteratorType
  zero : terms.term Base
  successor : terms.term OrdinalFunction
  addition : terms.term BinaryOrdinalFunction
  multiplication : terms.term BinaryOrdinalFunction
  omega : terms.term Base
  power : terms.term OrdinalFunction
  fix : terms.term FixedPointFunction
  multiplicationStep : terms.term Base → terms.term OrdinalFunction
  powerStep : terms.term OrdinalFunction

def applyUnary {terms : TermStructure} (f : terms.term OrdinalFunction) (x : terms.term Base) :
    terms.term Base := terms.app Base Base f x

def applyBinary {terms : TermStructure} (f : terms.term BinaryOrdinalFunction)
    (a b : terms.term Base) : terms.term Base := applyUnary (terms.app Base OrdinalFunction f a) b

def applyIterator {terms : TermStructure} (op : ArithmeticTerms terms) (b : terms.term Base)
    (f : terms.term OrdinalFunction) (a : terms.term Base) : terms.term Base :=
  applyUnary (terms.app OrdinalFunction OrdinalFunction
    (terms.app Base FixedPointFunction op.iterator b) f) a

def literalOne {terms : TermStructure} (op : ArithmeticTerms terms) : terms.term Base :=
  applyUnary op.successor op.zero

def literalNext {terms : TermStructure} (op : ArithmeticTerms terms) : terms.term OrdinalFunction :=
  terms.app OrdinalFunction OrdinalFunction op.fix op.power

def finiteSuccessor {terms : TermStructure} (op : ArithmeticTerms terms) : Nat → terms.term Base
  | 0 => op.zero
  | n + 1 => applyUnary op.successor (finiteSuccessor op n)

def TwoStrictEdges {terms : TermStructure} (source target : terms.term Base) : Prop :=
  ∃ middle : terms.term Base, terms.below Base middle source ∧ terms.below Base target middle

/-- The literal base operations supply these particular original strict edges.
The hypotheses here concern the typed terms and their reductions only. -/
structure ArithmeticStrictEdges {terms : TermStructure} (op : ArithmeticTerms terms) : Prop where
  successor : ∀ a, TwoStrictEdges (applyUnary op.successor a) a
  addition : ∀ a b, TwoStrictEdges (applyBinary op.addition a b) (applyIterator op b op.successor a)
  multiplyStep : ∀ a x, terms.below Base (applyBinary op.addition x a) (applyUnary (op.multiplicationStep a) x)
  multiplication : ∀ a b,
    TwoStrictEdges (applyBinary op.multiplication a b) (applyIterator op b (op.multiplicationStep a) op.zero)
  omega : ∀ n, terms.below Base (finiteSuccessor op n) op.omega
  powerStep : ∀ x, terms.below Base (applyBinary op.multiplication x op.omega) (applyUnary op.powerStep x)
  power : ∀ a, terms.below Base (applyIterator op a op.powerStep (literalOne op)) (applyUnary op.power a)
  fix : ∀ f z, TwoStrictEdges (applyUnary (terms.app OrdinalFunction OrdinalFunction op.fix f) z)
    (applyIterator op op.omega f (applyUnary op.successor z))

def IteratorRealizesOrbit {terms : TermStructure} (wf : WellFounded (terms.below Base))
    (op : ArithmeticTerms terms) : Prop :=
  Realizes terms wf OrdinalIteratorType op.iterator (fun b f a => orbit Base f a b)

def ArithmeticOperationsRealize {terms : TermStructure} (wf : WellFounded (terms.below Base))
    (op : ArithmeticTerms terms) : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    Realizes terms wf Base op.zero Z ∧
    Realizes terms wf OrdinalFunction op.successor s ∧
    Realizes terms wf BinaryOrdinalFunction op.addition add ∧
    Realizes terms wf BinaryOrdinalFunction op.multiplication mul ∧
    Realizes terms wf Base op.omega w ∧ Realizes terms wf Base (literalOne op) one ∧
    Realizes terms wf OrdinalFunction op.power pow ∧
    Realizes terms wf FixedPointFunction op.fix fix ∧
    Realizes terms wf OrdinalFunction (literalNext op) (fix pow)

def ArithmeticRealizationComposition : Prop :=
  ∀ (terms : TermStructure) (wf : WellFounded (terms.below Base)) (op : ArithmeticTerms terms),
    StrictFunctionSlot terms → ArithmeticStrictEdges op → IteratorRealizesOrbit wf op →
      ArithmeticOperationsRealize wf op

end LogicLineages.PersistentMarking.OrdinalArithmeticRealizationTargets
