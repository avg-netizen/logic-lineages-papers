module

public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalCode
open GorbowSyntax GorbowSortedSyntaxCode GorbowDiagonalSentence
open LogicLineages.ComputabilityKnowledge.GorbowDiagonalCode

def RawExact : Prop := ∀ raw out, thetaRaw raw=some out ↔ ∃ φ : Formula 1,
  raw=GorbowFormulaPrefixCode.encode φ ∧ out=GorbowFormulaPrefixCode.encode (theta φ)

def NumericExact : Prop := ∀ code out, output code=some out ↔ ∃ φ : Formula 1,
  code=formulaCode φ ∧ out=formulaCode (diagonal φ)

def Calibration : Prop := ∀ φ : Formula 1,
  output (formulaCode φ)=some (formulaCode (diagonal φ))

def Rejection : Prop := ∀ code, output code=none ↔ ¬ ∃ φ : Formula 1, code=formulaCode φ

def ProvedOutput : Prop := ∀ (φ : Formula 1) out, output (formulaCode φ)=some out →
  Nonempty (GorbowTheoryProof.Derivation Theory
    (GorbowBooleanTruth.biconditional (diagonal φ)
      (GorbowStandardInstances.instantiate φ (Term.numeral out))))

def UniformPrograms : Prop := Primrec thetaRaw ∧ Primrec output

def Target : Prop := RawExact ∧ NumericExact ∧ Calibration ∧ Rejection ∧ ProvedOutput ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalCode
