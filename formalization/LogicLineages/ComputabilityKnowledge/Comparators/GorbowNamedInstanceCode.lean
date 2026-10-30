module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedInstanceCode
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowCodeConstructors GorbowFormulaComposition
open LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCode

def OriginalCalibration : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  ∀ t : Term 0, instanceNumber v.val (formulaNumber φ) (termNumber t)=some (formulaNumber (namedClosedInstance v φ t))

def ExactOutput : Prop := ∀ v formulaCode termCode out, instanceNumber v formulaCode termCode=some out ↔
  ∃ (n : Nat) (φ : Formula n) (hv : v<n) (t : Term 0),
    formulaCode=formulaNumber φ ∧ formulaSupport φ={v} ∧ termCode=termNumber t ∧
    out=formulaNumber (namedClosedInstance ⟨v,hv⟩ φ t)

def OutputDomain : Prop := ∀ v formulaCode termCode out, instanceNumber v formulaCode termCode=some out →
  ∃ σ : Sentence, out=formulaNumber σ

def OriginalSemantics : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  ∀ t : Term 0, ∃ σ : Sentence,
    instanceNumber v.val (formulaNumber φ) (termNumber t)=some (formulaNumber σ) ∧
    ∀ I ρ, σ.realize I Fin.elim0 ↔ φ.realize I (assignAt ρ v (t.realize I Fin.elim0))

def ExactRejection : Prop := ∀ v formulaCode termCode,
  instanceNumber v formulaCode termCode=none ↔
    GorbowNamedNumericCode.namedInput v formulaCode=none ∨ GorbowClosedTermCode.fullTermCode termCode=false

def UniformProgram : Prop := Primrec (fun p : Nat × Nat × Nat => instanceNumber p.1 p.2.1 p.2.2)

def Target : Prop := OriginalCalibration ∧ ExactOutput ∧ OutputDomain ∧ OriginalSemantics ∧ ExactRejection ∧ UniformProgram
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedInstanceCode
