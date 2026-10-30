module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedNamedCode
open GorbowSyntax GorbowSortedSyntaxCode GorbowFreeSupport GorbowNamedBinding GorbowFormulaComposition
open LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCode

def InputCalibration : Prop := ∀ n (φ : Formula n) (v : Fin n),
  decodeInputs (variableNumber v.val) (formulaCode φ)=some (v.val,GorbowCodeConstructors.formulaNumber φ)

def ExactNamedDomain : Prop := ∀ varCode formula, namedFormula varCode formula=true ↔
  ∃ (n : Nat) (φ : Formula n) (v : Fin n),
    varCode=variableNumber v.val ∧ formula=formulaCode φ ∧ formulaSupport φ={v.val}

def OriginalCalibration : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  allNumber (variableNumber v.val) (formulaCode φ)=some (formulaCode (bindAll v φ)) ∧
  exNumber (variableNumber v.val) (formulaCode φ)=some (formulaCode (bindEx v φ)) ∧
  ∀ t : Term 0, instanceNumber (variableNumber v.val) (formulaCode φ) (termCode t)=
    some (formulaCode (namedClosedInstance v φ t))

def ExactDefinedness : Prop := ∀ varCode formula,
  ((allNumber varCode formula).isSome=true ↔ namedFormula varCode formula=true) ∧
  ((exNumber varCode formula).isSome=true ↔ namedFormula varCode formula=true) ∧
  (∀ term, (instanceNumber varCode formula term).isSome=true ↔
    namedFormula varCode formula=true ∧ GorbowSortedBooleanCode.fullTermCode term=true)

def OutputDomains : Prop := ∀ varCode formula out,
  (allNumber varCode formula=some out → ∃ σ : Sentence,out=formulaCode σ) ∧
  (exNumber varCode formula=some out → ∃ σ : Sentence,out=formulaCode σ) ∧
  (∀ term, instanceNumber varCode formula term=some out → ∃ σ : Sentence,out=formulaCode σ)

def OriginalSemantics : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  ∃ σ τ : Sentence,
    allNumber (variableNumber v.val) (formulaCode φ)=some (formulaCode σ) ∧
    exNumber (variableNumber v.val) (formulaCode φ)=some (formulaCode τ) ∧
    ∀ I ρ, (σ.realize I Fin.elim0 ↔ ∀ x,φ.realize I (assignAt ρ v x)) ∧
      (τ.realize I Fin.elim0 ↔ ∃ x,φ.realize I (assignAt ρ v x))

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => decodeInputs p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => namedFormula p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => allNumber p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => exNumber p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × Nat => instanceNumber p.1 p.2.1 p.2.2)

def Target : Prop := InputCalibration ∧ ExactNamedDomain ∧ OriginalCalibration ∧ ExactDefinedness ∧ OutputDomains ∧ OriginalSemantics ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedNamedCode
