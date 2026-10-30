module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicParameters

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicParameters
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowSortedRevision GorbowRegistryTuple
open LogicLineages.ComputabilityKnowledge.GorbowAtomicParameters

def GuardCalibration : Prop := ∀ n (t : Term n) P ρ,
  (GorbowSortedQuantifierTruth.arithmeticTermGuard t).realize (interpretation GorbowAtomicRegistry.ground P) ρ ↔
    GorbowSortedBooleanCode.arithmeticTermCode (t.realize (interpretation GorbowAtomicRegistry.ground P) ρ)=true

def ClosureSemantics : Prop := ∀ n (φ : Formula n) P,
  (arithmeticClosure φ).realize (interpretation GorbowAtomicRegistry.ground P) Fin.elim0 ↔
    ∀ ρ : Fin n → Nat, (∀ i, GorbowSortedBooleanCode.arithmeticTermCode (ρ i)=true) →
      φ.realize (interpretation GorbowAtomicRegistry.ground P) ρ

def EvaluationCalibration : Prop := ∀ n (t : Term n) P ρ (s : Term 0), ArithmeticTerm s →
  t.realize (interpretation GorbowAtomicRegistry.ground P) ρ=termCode s →
  (evaluationTerm t).realize (interpretation GorbowAtomicRegistry.ground P) ρ=
    s.realize (interpretation GorbowAtomicRegistry.ground P) Fin.elim0

def DictionaryCalibration : Prop := ∀ n m (names : Fin n → Fin m), Function.Injective names →
  ∀ (ts : Fin n → Term 0), (∀ j, ArithmeticTerm (ts j)) → ∀ P ρ,
  (∀ j, ρ j=termCode (ts j)) →
  (∀ i, (codeDictionary names i).realize (interpretation GorbowAtomicRegistry.ground P) ρ=
    termCode (GorbowNameDictionary.dictionary names ts i)) ∧
  (∀ i, (valueDictionary names i).realize (interpretation GorbowAtomicRegistry.ground P) ρ=
    (GorbowNameDictionary.dictionary names ts i).realize (interpretation GorbowAtomicRegistry.ground P) Fin.elim0) ∧
  (argumentTuple names).realize (interpretation GorbowAtomicRegistry.ground P) ρ=
    tuple (List.ofFn (fun i => termCode (GorbowNameDictionary.dictionary names ts i)))

def Target : Prop := GuardCalibration ∧ ClosureSemantics ∧ EvaluationCalibration ∧ DictionaryCalibration
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicParameters
