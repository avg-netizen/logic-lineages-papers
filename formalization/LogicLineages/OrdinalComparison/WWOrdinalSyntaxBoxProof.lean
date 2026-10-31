module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem vector_lookup {Γ : List Ty} {m : Nat} (v : OrdinalVector Γ m) (i : Nat) :
    (vectorCode v).getD i 0 = typedCode (ordinalVectorAt v i) := by
  by_cases hi : i < m+1
  · simp only [vectorCode, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hi, ordinalVectorAt]
  · simp [vectorCode, List.getD_eq_getElem?_getD, hi, ordinalVectorAt, typedCode, code]

private theorem positive_correct (Γ : List Ty) (m n : Nat)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n) (i : Nat) :
    boxPositive n (vectorCode f) (vectorCode g) i =
      typedCode (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i) := by
  rw [boxPositive, ordinalBoxPositive]
  by_cases hi : i ≤ n
  · rw [dif_pos hi, dif_pos hi, positive_correct Γ m n f g (i+1), vector_lookup, vector_lookup]
    rfl
  · rw [dif_neg hi, dif_neg hi, vector_lookup]
termination_by n+1-i
decreasing_by omega

theorem ordinalSyntaxBoxPositiveCorrect : Targets.OrdinalSyntaxBoxPositiveCorrect := positive_correct

private theorem tail_correct {Γ : List Ty} (n : Nat) (f g : OrdinalExpression Γ) :
    boxTail n (typedCode f) (typedCode g) = typedCode (AdmissibleAssignment.boxTail allLeftPolicy n f g) := by
  unfold boxTail AdmissibleAssignment.boxTail
  by_cases hn : n=0
  · simp [hn, typedCode, code, node]
  · simp only [if_neg hn]
    have hr := ordinalSyntaxRepeatCorrect Γ .numeral n (.one : OrdinalExpression Γ)
    change repeatCode n 1 = typedCode (AdmissibleAssignment.numeral allLeftPolicy n) at hr
    rw [hr]
    rfl

theorem ordinalSyntaxApplicationCorrect : Targets.OrdinalSyntaxApplicationCorrect := by
  intro Γ σ τ f g
  apply List.ext_getElem
  · simp [applicationCode, vectorCode]
  · intro j hj hk
    have hj' : j < τ.level+1 := by simpa [applicationCode] using hj
    simp only [applicationCode, vectorCode, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    unfold AdmissibleAssignment.application AdmissibleAssignment.box
    by_cases hzero : j=0
    · simp only [hzero, if_true]
      have hpos := positive_correct Γ _ _ f g 1
      dsimp only [vectorCode] at hpos
      rw [hpos]
      have hf : (List.ofFn (fun i => typedCode (f i))).getD 0 0 = typedCode (f 0) := by
        simp [List.getD_eq_getElem?_getD]
      have hg : (List.ofFn (fun i => typedCode (g i))).getD 0 0 = typedCode (g 0) := by
        simp [List.getD_eq_getElem?_getD]
      rw [hf, hg, tail_correct]
      rfl
    · simp only [if_neg hzero]
      exact positive_correct Γ _ _ f g j
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
