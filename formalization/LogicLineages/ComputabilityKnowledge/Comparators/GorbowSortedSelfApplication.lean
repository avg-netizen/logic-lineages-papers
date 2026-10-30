module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplication

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSelfApplication
open GorbowSyntax GorbowSortedSyntaxCode
open LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplication

def RawExact : Prop := ∀ raw out, rawSelf raw=some out ↔ ∃ φ : Formula 1,
  raw=GorbowFormulaPrefixCode.encode φ ∧ out=GorbowFormulaPrefixCode.encode (selfInstance φ)

def NumericExact : Prop := ∀ code out, selfApply code=some out ↔ ∃ φ : Formula 1,
  code=formulaCode φ ∧ out=formulaCode (selfInstance φ)

def Calibration : Prop := ∀ φ : Formula 1,
  selfApply (formulaCode φ)=some (formulaCode (selfInstance φ))

def Rejection : Prop := ∀ code, selfApply code=none ↔ ¬ ∃ φ : Formula 1,code=formulaCode φ

def UniformPrograms : Prop := Primrec rawSelf ∧ Primrec selfApply

def Target : Prop := RawExact ∧ NumericExact ∧ Calibration ∧ Rejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSelfApplication
