module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicTruth

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicTruth
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowSortedRevision
open GorbowNameDictionary GorbowRevisionComposition
open LogicLineages.ComputabilityKnowledge.GorbowAtomicTruth

def CodeCalibration : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  Function.Injective names → ∀ (ts : Fin n → Term 0), (∀ j, ArithmeticTerm (ts j)) → ∀ P ρ,
  (∀ j, ρ j=termCode (ts j)) →
  (instanceCodeTerm R names).realize (interpretation GorbowAtomicRegistry.ground P) ρ=
    formulaCode (GorbowFormulaSubstitution.substituteFormula (dictionary names ts) R)

def AtomicSchemas : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  AtomicMinus R → Function.Injective names → Covers R names → ∀ initial k,
  (atomicAxiom R names).realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0

def OtherCodedClauses : Prop := ∀ initial k,
  GorbowBooleanTruth.negAxiom.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0 ∧
  GorbowBooleanTruth.impAxiom.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0 ∧
  GorbowBooleanTruth.conjAxiom.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0 ∧
  GorbowBooleanTruth.disjAxiom.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0 ∧
  GorbowSortedQuantifierTruth.forallAxiom.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0 ∧
  GorbowSortedQuantifierTruth.existsAxiom.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0 ∧
  GorbowSortedQuantifierTruth.barcanAxiom.realize (stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0

def Target : Prop := CodeCalibration ∧ AtomicSchemas ∧ OtherCodedClauses
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicTruth
