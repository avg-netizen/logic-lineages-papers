module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchTargets
import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchHeadProof
import LogicLineages.OrdinalComparison.CanonicalGuardSelector.BridgeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchProof
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector
open OuterShiftNormalization DispatchLocalProof

theorem dispatchCorrect : DispatchTargets.DispatchCorrect := by
  intro D A B q hA hB hsel x y hx hy
  have hcA : coreWord A ≠ [] := by
    intro h
    have he : coreWord A = [] ∨ coreWord B = [] := Or.inl h
    rw [selectWords,if_pos he] at hsel
    cases hsel
  have hcB : coreWord B ≠ [] := by
    intro h
    have he : coreWord A = [] ∨ coreWord B = [] := Or.inr h
    rw [selectWords,if_pos he] at hsel
    cases hsel
  have hnone : ¬ (coreWord A = [] ∨ coreWord B = []) := by
    intro h
    exact h.elim hcA hcB
  have hq : selectHeads (viewPrefix A) (viewHead A) (viewPrefix B) (viewHead B) = q := by
    simpa only [selectWords,if_neg hnone,Option.some.injEq] using hsel
  have hx' : wordTail A ≤ x ∧ wordTail B ≤ x ∧
      headTail (viewPrefix A) (viewHead A) (viewPrefix B) (viewHead B)
        (outerShift A) (outerShift B) ≤ x := by
    simpa only [dispatchTail,max_le_iff] using hx
  have hy' : wordTail A ≤ y ∧ wordTail B ≤ y ∧
      headTail (viewPrefix A) (viewHead A) (viewPrefix B) (viewHead B)
        (outerShift A) (outerShift B) ≤ y := by
    simpa only [dispatchTail,max_le_iff] using hy
  have hAx := CanonicalGuardSelector.Proof.viewTailCorrect D A x hA hx'.1
  have hBy := CanonicalGuardSelector.Proof.viewTailCorrect D B y hB hy'.2.1
  have hvA := CanonicalGuardSelector.Proof.viewSyntax D A hA
  have hvB := CanonicalGuardSelector.Proof.viewSyntax D B hB
  have hl := DispatchHeadProof.headCorrect D
    (viewPrefix A) (viewHead A) (viewPrefix B) (viewHead B)
    (outerShift A) (outerShift B)
    hvA.1 hvA.2.1 hvA.2.2.1 hvA.2.2.2.1
    hvB.1 hvB.2.1 hvB.2.2.1 hvB.2.2.2.1 x y hx'.2.2 hy'.2.2
  dsimp only at hl
  rw [hq] at hl
  have hp : Result (preparedWord A) (preparedWord B)
      q.2.2.1 q.2.2.2 (dispatchTie A B) x y := by
    simpa only [preparedWord,if_neg hcA,if_neg hcB,dispatchTie] using hl
  refine ⟨hAx.1,hBy.1,hAx.2.1,hBy.2.1,hp.2.2.1,hp.2.2.2.1,?_⟩
  have he := hp.2.2.2.2
  rw [hAx.2.2,hBy.2.2] at he
  exact he

theorem dispatchChild : DispatchTargets.DispatchChild :=
  CanonicalGuardSelector.Proof.selectedChildCorrect

theorem dispatchTieBound : DispatchTargets.DispatchTieBound :=
  DispatchOrderProof.dispatchTieBound

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchProof
