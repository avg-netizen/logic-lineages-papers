import LogicLineages.PersistentMarking.NativeTowerWitnessPrefixTargets
import LogicLineages.PersistentMarking.NativeTowerExtractorTypingProof
import LogicLineages.PersistentMarking.NativeOrdinalExponentialTypingProof
import LogicLineages.PersistentMarking.NativeClosedApplication
import LogicLineages.PersistentMarking.NativeTypingProof

namespace LogicLineages.PersistentMarking.NativeTowerWitnessPrefixProof
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeCarrierTargets NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets
open NativeTowerExtractorTargets NativeTowerExtractorTypingProof NativeTowerWitnessPrefixTargets

def ClosedPrefix.lower : {n : Nat} → ClosedPrefix S n →
    ClosedNativeTerm S (ty (n+2)) → ClosedNativeTerm S (ty 2)
  | 0, .first _, q => q
  | n+1, .extend previous _, q => lower previous (applyClosed q previous.top)

theorem topLiteral (p : ClosedPrefix S n) : p.top.val = p.raw.top := by
  cases p <;> rfl

theorem loweredLiteral (p : ClosedPrefix S n) (q : ClosedNativeTerm S (ty (n+2))) :
    (ClosedPrefix.lower p q).val = p.raw.lower q.val := by
  revert q
  induction p with
  | first a => intro q; rfl
  | extend p a ih =>
    intro q
    change (ClosedPrefix.lower p (applyClosed q p.top)).val =
      p.raw.lower (app _ _ q.val p.raw.top)
    simpa only [← topLiteral p, applyClosed] using ih (applyClosed q p.top)

def nativeNb (S : Signature) : ClosedNativeTerm S endo := ⟨nativeNB,nativeNBClosed S⟩

def nativeOmega (S : Signature) : ClosedNativeTerm S indexType :=
  ⟨omegaCarrier,NativeOrdinalExponentialTypingProof.omegaClosed S⟩

def closedT0 (S : Signature) : ClosedNativeTerm S indexType := applyClosed (nativeNb S) (nativeOmega S)
def closedT1 (S : Signature) : ClosedNativeTerm S indexType := applyClosed (nativeNb S) (closedT0 S)

def closedLater (p : ClosedPrefix S n) : ClosedNativeTerm S indexType :=
  applyClosed (applyClosed (ClosedPrefix.lower p p.top) (nativeNb S)) (closedT0 S)

theorem laterLiteral (p : ClosedPrefix S n) : (closedLater p).val = later p.raw := by
  change app indexType indexType
      (app endo endo (ClosedPrefix.lower p p.top).val nativeNB) t0 = later p.raw
  simp only [loweredLiteral, topLiteral, later]

theorem laterClosed (p : ClosedPrefix S n) : ClosedNative S (later p.raw) indexType := by
  rw [← laterLiteral p]
  exact (closedLater p).property

private def closedPrefix0 (S : Signature) : ClosedPrefix S 0 :=
  .first ⟨extractorZero,extractorZeroClosed S⟩

private def closedPrefix1 (S : Signature) : ClosedPrefix S 1 :=
  .extend (closedPrefix0 S) ⟨extractorOne,extractorOneClosed S⟩

theorem exact_FirstFourTowerWitnesses : ExactFirstFourTowerWitnesses := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro S
  exact ⟨(closedT0 S).property,(closedT1 S).property,laterClosed (closedPrefix0 S),
    laterClosed (closedPrefix1 S)⟩

private theorem selectRight (f : ClosedNativeTerm S (.arrow τ τ)) (a : ClosedNativeTerm S τ) :
    NativeBelow a (applyClosed f a) := by
  let start := applyClosed f a
  change ConfinedPair.Strict S start.val a.val
  exact ⟨⟨τ,start.property.1.1,a.property.1.1,start.property.1.2.1,a.property.1.2.1⟩,
    .intro start.property.1.1 a.property.1.1 rfl
      (NativeTypingProof.secondSelect S τ τ f.val a.val .nil
        f.property.1.1 a.property.1.1 a.property.1.2.1 .nil True.intro),
    NativeTypingProof.rightIncluded τ τ f.val a.val⟩

theorem laterSelectsT0 (p : ClosedPrefix S n) : ConfinedPair.Strict S (later p.raw) t0 := by
  rw [← laterLiteral p]
  exact selectRight (applyClosed (ClosedPrefix.lower p p.top) (nativeNb S)) (closedT0 S)

theorem exact_FirstFourTowerArgumentEdges : ExactFirstFourTowerArgumentEdges := by
  intro S
  exact ⟨selectRight (nativeNb S) (nativeOmega S),
    selectRight (nativeNb S) (closedT0 S),laterSelectsT0 (closedPrefix0 S),laterSelectsT0 (closedPrefix1 S)⟩

#print axioms loweredLiteral
#print axioms laterLiteral
#print axioms laterClosed
#print axioms exact_FirstFourTowerWitnesses
#print axioms laterSelectsT0
#print axioms exact_FirstFourTowerArgumentEdges
end LogicLineages.PersistentMarking.NativeTowerWitnessPrefixProof
