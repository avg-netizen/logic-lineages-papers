module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullbackTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback.Proof
open FirstOrder Language CotreePresburger

@[simp] theorem wordCounts_nil {A : Type} [DecidableEq A] (a : A) :
    wordCounts ([] : List A) a = 0 := rfl

@[simp] theorem wordCounts_cons {A : Type} [DecidableEq A] (x : A) (xs : List A) (a : A) :
    wordCounts (x :: xs) a = wordCounts xs a + if x = a then 1 else 0 := by
  simp [wordCounts, List.countP_cons]

theorem wordCountsEqCount : Targets.WordCountsEqCount := by
  intro A _ _ _ xs a
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [wordCounts_cons, List.count_cons, beq_iff_eq, ih]

theorem pushWordCountsExact : Targets.PushWordCountsExact := by
  intro Q R _ _ _ f xs q
  induction xs with
  | nil => simp [pushCounts]
  | cons x xs ih =>
    have hstep : pushCounts f (wordCounts (x :: xs)) q =
        pushCounts f (wordCounts xs) q + if f x = q then 1 else 0 := by
      unfold pushCounts
      simp only [wordCounts_cons, CotreeGrammarFlow.Proof.indicator_add, Finset.sum_add_distrib]
      congr 1
      calc
        _ = ∑ r : R, if r = x then (if f x = q then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          by_cases h : r = x
          · subst r; simp
          · simp [h, Ne.symm h]
        _ = _ := by simp
    rw [hstep, ih]
    simp

@[simp] theorem realize_pullTerm {Q R : Type} [DecidableEq Q] [Fintype R] [LinearOrder R]
    (f : R → Q) (q : Q) (counts : R → Nat) :
    (pullTerm f q).realize counts = pushCounts f counts q := by
  simp [pullTerm, pushCounts]

theorem pullFormulaExact : Targets.PullFormulaExact := by
  intro Q R _ _ _ f φ counts
  simp [pullFormula]

theorem pullWordExact : Targets.PullWordExact := by
  intro Q R _ _ _ f φ xs
  rw [pullFormulaExact]
  have h : pushCounts f (wordCounts xs) = wordCounts (xs.map f) :=
    funext (pushWordCountsExact Q R f xs)
  rw [h]

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullback.Proof
