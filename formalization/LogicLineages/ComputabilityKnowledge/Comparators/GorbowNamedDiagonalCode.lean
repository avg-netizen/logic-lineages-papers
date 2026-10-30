module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedDiagonalCode
open GorbowSyntax GorbowSortedSyntaxCode GorbowFreeSupport GorbowNamedBinding GorbowDiagonalSentence
open LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalCode

def SelectionCalibration : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  select (variableNumber v.val) (formulaCode φ)=some (formulaCode (selectVariable v φ))

def OriginalCalibration : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  output (variableNumber v.val) (formulaCode φ)=some (formulaCode (diagonal (selectVariable v φ)))

def ExactOutput : Prop := ∀ varCode formula out, output varCode formula=some out ↔
  ∃ n, ∃ (φ : Formula n) (v : Fin n), varCode=variableNumber v.val ∧ formula=formulaCode φ ∧
    formulaSupport φ={v.val} ∧ out=formulaCode (diagonal (selectVariable v φ))

def Rejection : Prop := ∀ varCode formula,
  output varCode formula=none ↔ GorbowSortedNamedCode.namedFormula varCode formula=false

def ProvedOutput : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  ∀ out, output (variableNumber v.val) (formulaCode φ)=some out →
  Nonempty (GorbowTheoryProof.Derivation Theory (GorbowBooleanTruth.biconditional
    (diagonal (selectVariable v φ))
    (GorbowFormulaComposition.namedClosedInstance v φ (Term.numeral out))))

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => select p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => output p.1 p.2)

def Target : Prop := SelectionCalibration ∧ OriginalCalibration ∧ ExactOutput ∧ Rejection ∧ ProvedOutput ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedDiagonalCode
