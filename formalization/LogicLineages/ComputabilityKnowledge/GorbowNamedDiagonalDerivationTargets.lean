module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation.Targets
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowTheoryProof
open GorbowDiagonalSentence GorbowPRProgram
open GorbowNamedDefiningTheory (Theory)

def CalibratedExistence : Prop := ∃ pF pR : Program 1, Calibrated pF pR

def ClosedEquation : Prop := ∀ (pF pR : Program 1), Calibrated pF pR → ∀ φ : Formula 1,
  Nonempty (Derivation (n:=0) (Theory pF pR)
    (.equal (deltaTerm (Term.numeral (formulaCode (theta φ))))
      (Term.numeral (formulaCode (diagonal φ)))))

def FixedPoint : Prop := ∀ (pF pR : Program 1), Calibrated pF pR → ∀ φ : Formula 1,
  Nonempty (Derivation (n:=0) (Theory pF pR) (GorbowBooleanTruth.biconditional
    (diagonal φ) (instantiate φ (Term.numeral (formulaCode (diagonal φ))))))

def OriginalName : Prop := ∀ (pF pR : Program 1), Calibrated pF pR →
  ∀ n (v : Fin n) (φ : Formula n), GorbowFreeSupport.formulaSupport φ = {v.val} →
  Nonempty (Derivation (n:=0) (Theory pF pR) (GorbowBooleanTruth.biconditional
    (diagonal (GorbowNamedBinding.selectVariable v φ))
    (GorbowFormulaComposition.namedClosedInstance v φ
      (Term.numeral (formulaCode (diagonal (GorbowNamedBinding.selectVariable v φ)))))))

def Consistency : Prop := ∀ pF pR : Program 1,
  ¬ Nonempty (Derivation (n:=0) (Theory pF pR) falseEquality)

end LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation.Targets
