import LogicLineages.PersistentMarking.NativeTowerWitnessFamilyTargets
import LogicLineages.PersistentMarking.NativeTowerExtractorGeneralProof
import LogicLineages.PersistentMarking.NativeTowerWitnessPrefixProof

namespace LogicLineages.PersistentMarking.NativeTowerWitnessFamilyProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeTowerExtractorGeneralTargets NativeTowerExtractorGeneralProof
open NativeTowerWitnessPrefixTargets NativeTowerWitnessPrefixProof NativeTowerWitnessFamilyTargets

def certifiedPrefix (S : Signature) : (l : Nat) → ClosedPrefix S l
  | 0 => .first ⟨extractor 0,extractorClosed S 0⟩
  | l+1 => .extend (certifiedPrefix S l) ⟨extractor (l+1),extractorClosed S (l+1)⟩

theorem literalPrefixExact (S : Signature) (l : Nat) :
    (certifiedPrefix S l).raw = literalPrefix l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [certifiedPrefix,ClosedPrefix.raw,literalPrefix,ih]

theorem literalPrefixTop (l : Nat) : (literalPrefix l).top = extractor l := by
  cases l <;> rfl

theorem printedLowerExact (l : Nat) (q : Expr) : (literalPrefix l).lower q = printedLower l q := by
  revert q
  induction l with
  | zero => intro q; rfl
  | succ l ih =>
    intro q
    simp only [literalPrefix,RawPrefix.lower,printedLower,literalPrefixTop,ih]

theorem exact_PrintedNativeTowerSyntax : ExactPrintedNativeTowerSyntax := by
  obtain ⟨at0,at1,_⟩ := exact_GeneralNativeExtractorFamily
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · simp only [towerTerm,literalPrefix,at0,t2,p0]
  · simp only [towerTerm,literalPrefix,at0,at1,t3,p1,p0]
  · intro l
    simp only [towerTerm,later,literalPrefixTop,printedLowerExact]

def closedTower (S : Signature) : (n : Nat) → ClosedNativeTerm S indexType
  | 0 => closedT0 S
  | 1 => closedT1 S
  | l+2 => closedLater (certifiedPrefix S l)

theorem closedTowerLiteral (S : Signature) (n : Nat) :
    (closedTower S n).val = towerTerm n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ l => simp only [closedTower,towerTerm,laterLiteral,literalPrefixExact]

theorem exact_ClosedNativeTowerFamily : ExactClosedNativeTowerFamily := by
  intro S n
  rw [← closedTowerLiteral S n]
  exact (closedTower S n).property

theorem exact_NativeTowerFinalOperand : ExactNativeTowerFinalOperand := by
  intro S n
  cases n with
  | zero =>
    exact ⟨(nativeOmega S).property,(exact_FirstFourTowerArgumentEdges S).1⟩
  | succ n =>
    cases n with
    | zero =>
      exact ⟨(closedT0 S).property,(exact_FirstFourTowerArgumentEdges S).2.1⟩
    | succ l =>
      refine ⟨(closedT0 S).property,?_⟩
      simpa only [towerTerm, finalOperand, literalPrefixExact] using laterSelectsT0 (certifiedPrefix S l)

#print axioms literalPrefixExact
#print axioms printedLowerExact
#print axioms closedTowerLiteral
#print axioms exact_PrintedNativeTowerSyntax
#print axioms exact_ClosedNativeTowerFamily
#print axioms exact_NativeTowerFinalOperand
end LogicLineages.PersistentMarking.NativeTowerWitnessFamilyProof
