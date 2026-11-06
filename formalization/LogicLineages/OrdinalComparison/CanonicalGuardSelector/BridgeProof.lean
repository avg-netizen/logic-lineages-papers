module
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.ViewProof
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.LocalProof
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.ChildrenProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
open PolynomialGraphCompletion OuterShiftNormalization GuardChildMeasureCompletion

theorem caseSound : Targets.CaseSound := by
  intro D code rev next current h
  induction h with
  | counterCounter A B n m c e j k hn hm =>
      exact ⟨by omega,by omega,GuardChild.counterCounter A B n m c e j k hn hm⟩
  | counterRange A B a n c j k ha hr hn =>
      exact ⟨by omega,by omega,GuardChild.counterRange A B a n c j k ha hr hn⟩
  | phiRange A B a j k ha hr =>
      exact ⟨by omega,by omega,GuardChild.phiRange A B a j k ha hr⟩
  | quadratic A B j k a b =>
      exact ⟨by omega,by omega,GuardChild.quadratic A B j k a b⟩
  | equalRank A B d c e j k a b hd hD =>
      exact ⟨by omega,by omega,GuardChild.equalRank A B d c e j k a b hd hD⟩
  | mixedKernel A B n m c e j k a b hD =>
      exact ⟨by omega,by omega,GuardChild.mixedKernel A B n m c e j k a b hD⟩
  | mixedQuadratic A B m c j k a b hD =>
      exact ⟨by omega,by omega,GuardChild.mixedQuadratic A B m c j k a b hD⟩
  | reverse _h ih => exact ⟨ih.1,ih.2.1,GuardChild.swap ih.2.2⟩

theorem selectionCoverage : Targets.SelectionCoverage := by
  intro A B
  have hA := (OuterShiftNormalization.Proof.splitSyntax A).2.2.2
  have hB := (OuterShiftNormalization.Proof.splitSyntax B).2.2.2
  by_cases h : coreWord A = [] ∨ coreWord B = []
  · rw [selectWords,if_pos h]
    constructor
    · intro _
      exact h.elim (fun h => Or.inl (hA.mp h)) (fun h => Or.inr (hB.mp h))
    · intro _
      rfl
  · rw [selectWords,if_neg h]
    constructor
    · intro he
      cases he
    · intro hs
      exact (h (hs.elim (fun hs => Or.inl (hA.mpr hs))
        (fun hs => Or.inr (hB.mpr hs)))).elim

theorem selectedChildCorrect : Targets.SelectedChildCorrect := by
  intro D A B q hA hB hsel
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
  have hvA := viewSyntax D A hA
  have hvB := viewSyntax D B hB
  have hl := localSelectionCorrect D (viewPrefix A) (viewHead A)
    (viewPrefix B) (viewHead B) (outerShift A) (outerShift B)
    hvA.1 hvA.2.1 hvA.2.2.1 hvA.2.2.2.1
    hvB.1 hvB.2.1 hvB.2.2.1 hvB.2.2.2.1
  dsimp only at hl
  rw [hq] at hl
  have hcert : GuardCase D q.1 q.2.1 q.2.2 (preparedWord A,preparedWord B) := by
    simpa only [preparedWord,if_neg hcA,if_neg hcB] using hl.1
  have hchild := (caseSound D q.1 q.2.1 q.2.2 (preparedWord A,preparedWord B) hcert).2.2
  have hdec := GuardChildMeasureCompletion.Proof.actualGuardChildDecrease D q.2.2
    (preparedWord A,preparedWord B) hchild
  have hdec' : ChildDecrease D q.2.2 (A,B) := by
    unfold ChildDecrease at hdec ⊢
    rwa [viewMeasure D A B hA hB] at hdec
  exact ⟨hcert,hdec',hl.2.1,hl.2.2⟩

end LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
