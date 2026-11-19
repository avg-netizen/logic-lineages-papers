import LogicLineages.PersistentMarking.NativeIndexedCarrierTargets
import LogicLineages.PersistentMarking.NativeClosedProof

namespace LogicLineages.PersistentMarking.NativeIndexedTypingThinProof
open Spine NameBridge TypeSupport NativeReduction NativeTypingProof
open NativeCarrierTargets NativeIndexedCarrierTargets

theorem erased (S : Signature) (A : SemanticType) (i : Expr) (hi : ClosedNative S i indexType) :
    ClosedNative S (erase A i) (actualType A) := by
  induction A with
  | base => exact hi
  | arrow a d _ ih => exact NativeClosedProof.lambda S (actualType a) (actualType d) (erase d i) ih

theorem discardClosed (S : Signature) (η : Ty) : ClosedNative S (discard η) (.arrow η (.arrow η η)) :=
  ⟨⟨⟨.lam (.lam (.bound rfl)),True.intro⟩,True.intro,fun _ => rfl⟩,
    by simp [Native,NativeIndexedCarrierTargets.discard,DecisionInventory.heads]⟩

theorem leftClosed (S : Signature) (η : Ty) (P : Expr) (hP : ClosedNative S P η) :
    ClosedNative S (left η P) (.arrow η η) :=
  NativeClosedProof.application S η (.arrow η η) _ P (discardClosed S η) hP

theorem kClosed (S : Signature) (A : SemanticType) (P i : Expr)
    (hP : ClosedNative S P (.arrow (actualType A) (actualType A))) (hi : ClosedNative S i indexType) :
    ClosedNative S (K A P i) (.arrow (actualType A) (actualType A)) := by
  let η := Ty.arrow (actualType A) (actualType A)
  exact NativeClosedProof.application S η η _ _ (leftClosed S η P hP) (erased S (.arrow A A) i hi)

theorem indexedClosed (S : Signature) (A : SemanticType) (P U i : Expr)
    (hP : ClosedNative S P (.arrow (actualType A) (actualType A)))
    (hU : ClosedNative S U (actualType A)) (hi : ClosedNative S i indexType) :
    ClosedNative S (indexedW A P U i) (actualType A) :=
  NativeClosedProof.carrier S (actualType A) (K A P i) U (kClosed S A P i hP hi) hU

theorem supportP (A : SemanticType) (P i : Expr) : Included P (K A P i) := by
  let η := Ty.arrow (actualType A) (actualType A)
  let e := erase (.arrow A A) i
  exact fun ρ h => leftIncluded η η (left η P) e ρ
    (rightIncluded η (.arrow η η) (discard η) P ρ h)

end LogicLineages.PersistentMarking.NativeIndexedTypingThinProof
