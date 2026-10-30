module

public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentence
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalSentence
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowTheoryProof
open LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentence

def LiteralBody : Prop := ∀ φ : Formula 1,
  diagonal φ = instantiate φ (deltaTerm (Term.numeral (formulaCode (theta φ))))

def ClosedEquation : Prop := ∀ φ : Formula 1, Nonempty (Derivation (n:=0) Theory
  (.equal (deltaTerm (Term.numeral (formulaCode (theta φ))))
    (Term.numeral (formulaCode (diagonal φ)))))

def FixedPoint : Prop := ∀ φ : Formula 1, Nonempty (Derivation Theory
  (GorbowBooleanTruth.biconditional (diagonal φ)
    (instantiate φ (Term.numeral (formulaCode (diagonal φ))))))

def OriginalName : Prop := ∀ n (v : Fin n) (φ : Formula n),
  GorbowFreeSupport.formulaSupport φ = {v.val} →
  Nonempty (Derivation Theory (GorbowBooleanTruth.biconditional
    (diagonal (GorbowNamedBinding.selectVariable v φ))
    (GorbowFormulaComposition.namedClosedInstance v φ
      (Term.numeral (formulaCode (diagonal (GorbowNamedBinding.selectVariable v φ)))))))

def ActualTheoryModel : Prop := ∀ (P : GorbowSortedRevision.Extension) n (φ : Formula n),
  Derivation Theory φ → ∀ ρ,
  φ.realize (GorbowSortedRevision.interpretation GorbowDiagonalRegistry.ground P) ρ

def Consistency : Prop := ¬ Nonempty (Derivation Theory falseEquality)

def UniformTheoryProgram : Prop := Primrec theoryProgram

def Target : Prop := LiteralBody ∧ ClosedEquation ∧ FixedPoint ∧ OriginalName ∧
  ActualTheoryModel ∧ Consistency ∧ UniformTheoryProgram
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalSentence
