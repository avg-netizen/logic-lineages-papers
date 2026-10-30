module

public import LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTuple

@[expose] public section

/-! Four literal universally coded Boolean truth axioms, using the concrete
U/u registry convention. This is not a representation theorem or a claim about
Base's defining axioms. Outer x is index 1 and inner y is index 0. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth
open GorbowSyntax GorbowRegistryTuple

def sentenceGuard {n : Nat} (t : Term n) : Formula n :=
  .universalRelation (headerTerm 1 0 [t])
def negCodeTerm {n : Nat} (t : Term n) : Term n :=
  .universalFunction (headerTerm 1 0 [t])
def binaryCodeTerm {n : Nat} (tag : Nat) (s t : Term n) : Term n :=
  .universalFunction (headerTerm 2 tag [s,t])
def biconditional {n : Nat} (φ ψ : Formula n) : Formula n := .conj (.imp φ ψ) (.imp ψ φ)

def negAxiom : Sentence := .all (.imp (sentenceGuard (.var 0))
  (biconditional (.truth (negCodeTerm (.var 0))) (.neg (.truth (.var 0)))))
def impAxiom : Sentence := .all (.all (.imp
  (.conj (sentenceGuard (.var 1)) (sentenceGuard (.var 0)))
  (biconditional (.truth (binaryCodeTerm 0 (.var 1) (.var 0))) (.imp (.truth (.var 1)) (.truth (.var 0))))))
def conjAxiom : Sentence := .all (.all (.imp
  (.conj (sentenceGuard (.var 1)) (sentenceGuard (.var 0)))
  (biconditional (.truth (binaryCodeTerm 1 (.var 1) (.var 0))) (.conj (.truth (.var 1)) (.truth (.var 0))))))
def disjAxiom : Sentence := .all (.all (.imp
  (.conj (sentenceGuard (.var 1)) (sentenceGuard (.var 0)))
  (biconditional (.truth (binaryCodeTerm 2 (.var 1) (.var 0))) (.disj (.truth (.var 1)) (.truth (.var 0))))))
end LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth
