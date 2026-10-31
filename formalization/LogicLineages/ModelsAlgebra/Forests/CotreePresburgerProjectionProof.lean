module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjectionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjection.Proof
open CotreePresburgerTransition

theorem count_cons_add {A : Type} [DecidableEq A] (x a : A) (w : List A) :
    (x :: w).count a = w.count a + if x = a then 1 else 0 := by
  simp only [List.count_cons, beq_iff_eq]

theorem projectedWordCounts : Targets.ProjectedWordCounts := by
  intro Q A _ _ _ _ label children B
  induction children with
  | nil => simp [projectedCounts]
  | cons x w ih =>
    have hstep : projectedCounts label (fun a => (x :: w).count a) B =
        projectedCounts label (fun a => w.count a) B + if label x = B then 1 else 0 := by
      unfold projectedCounts
      simp only [count_cons_add, CotreeGrammarFlow.Proof.indicator_add, Finset.sum_add_distrib]
      congr 1
      calc
        _ = ∑ a : A, if a = x then (if label x = B then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a = x
          · subst a; simp
          · simp [h, Ne.symm h]
        _ = _ := by simp
    rw [hstep, ih]
    simp [count_cons_add]

theorem wordTotalCounts : Targets.WordTotalCounts := by
  intro A _ _ children
  induction children with
  | nil => simp
  | cons x w ih =>
    simp only [count_cons_add, Finset.sum_add_distrib, ih, List.length_cons]
    simp

theorem allowedWordCounts : Targets.AllowedWordCounts := by
  intro A _ allowed children
  constructor
  · intro h a ha
    cases hv : allowed a with
    | false =>
      have hz := h a hv
      have hp := List.count_pos_iff.mpr ha
      omega
    | true => rfl
  · intro h a ha
    apply List.count_eq_zero.mpr
    intro hm
    have he := h a hm
    simp [ha] at he

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjection.Proof
