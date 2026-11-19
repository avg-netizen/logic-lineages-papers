import LogicLineages.PersistentMarking.NumberedWindowExternalIDTagProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalIDLeastProof
open NumberedWindowExternalIDOperators NumberedWindowExternalIDOperatorTargets
open NumberedWindowExternalIDTagProof

theorem leastFixed (F : Operator) (mono : IsMonotone F) (n : Nat) :
    F (Least F) n ↔ Least F n := by
  have closed : Below (F (Least F)) (Least F) := by
    intro c hc P hp
    have hBelow : Below (Least F) P := fun d hd => hd P hp
    exact hp c (mono _ _ hBelow c hc)
  have hImage : IsPrefixed F (F (Least F)) := mono _ _ closed
  exact ⟨closed n,fun h => h (F (Least F)) hImage⟩

theorem actualFixed : ActualLeastPredicatesFixed := by
  intro S K n
  exact ⟨leastFixed _ (scalarMono S K) n,leastFixed _ (multisetMono S K) n,
    leastFixed _ (taggedMono S K) n⟩

private theorem leastFiber (F A : Operator) (tag : Nat → Nat)
    (inj : Function.Injective tag)
    (proj : ∀ P n, F P (tag n) ↔ A (fun y => P (tag y)) n) (n : Nat) :
    Least F (tag n) ↔ Least A n := by
  constructor
  · intro h P hp
    let Q : Pred := fun c => ∀ d, c = tag d → P d
    have hRestrict : (fun d => Q (tag d)) = P := by
      funext d
      apply propext
      constructor
      · intro hd
        exact hd d rfl
      · intro hd e he
        have hEq : d = e := inj he
        exact hEq ▸ hd
    have hPreQ : IsPrefixed F Q := by
      intro c hc d hd
      have hF : F Q (tag d) := hd ▸ hc
      have hA := (proj Q d).mp hF
      rw [hRestrict] at hA
      exact hp d hA
    exact h Q hPreQ n rfl
  · intro h P hp
    have hPreA : IsPrefixed A (fun d => P (tag d)) := by
      intro d hd
      exact hp (tag d) ((proj P d).mpr hd)
    exact h _ hPreA

theorem actualProjection : ActualLeastTagProjection := by
  intro S K n
  exact ⟨leastFiber _ _ _ scalarInjective (scalarAt S K) n,
    leastFiber _ _ _ multisetInjective (multisetAt S K) n⟩

end LogicLineages.PersistentMarking.NumberedWindowExternalIDLeastProof
