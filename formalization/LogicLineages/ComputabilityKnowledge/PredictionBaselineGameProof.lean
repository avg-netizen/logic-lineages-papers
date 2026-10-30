module

public import LogicLineages.ComputabilityKnowledge.PredictionBaselineGameTargets
public import LogicLineages.ComputabilityKnowledge.PredictionRobustProof
public import LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBaselineGameProof
open PredictionGame PredictionLearning PredictionRobust PredictionSelfHistory
open PredictionBaselineGame PredictionBaselineGameTargets

private theorem pr_budgetPrefix (b : Nat → Nat) (hb : Primrec b) : Primrec (budgetPrefix b) := by
  have h := Primrec.list_map (Primrec.list_range.comp Primrec.succ) (hb.comp Primrec.snd).to₂
  apply h.of_eq
  intro n
  apply List.ext_getElem
  · simp [budgetPrefix, historyPrefix]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, budgetPrefix, historyPrefix, List.getElem_ofFn]

theorem primitiveRecursiveBudgetRule : PrimitiveRecursiveBudgetRule := by
  intro b hb
  exact PredictionRobustProof.primitiveRecursiveBaseline.comp
    (((pr_budgetPrefix b hb).comp (Primrec.list_length.comp Primrec.fst)).pair
      (Primrec.fst.pair Primrec.snd))

theorem baselineProgramRealization : BaselineProgramRealization := by
  intro b hb
  have hR := primitiveRecursiveBudgetRule b hb
  exact ⟨PredictionSelfHistoryProof.primitiveRecursiveSelfPolicy _ hR,
    PredictionSelfHistoryProof.ordinarySelfPolicyProgram _ hR⟩

private theorem prefix_snoc {α : Type} (s : Nat → α) (n : Nat) :
    historyPrefix s (n + 1) = historyPrefix s n ++ [s n] := by
  exact List.ofFn_succ_last

theorem actualBaselineLearning : ActualBaselineLearning := by
  intro b e hp hav
  let p := baselinePolicy b
  let q := policy e hp
  let y := prediction p q
  have hys : ∀ n, (histories p q n).predictions = historyPrefix y n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [prediction_prefix, ih, prefix_snoc]
  let x := fun n => q (historyPrefix y n)
  have hxval : ∀ n, x n = evasion p q n := by
    intro n
    change q (historyPrefix y n) = q (histories p q n).predictions
    rw [hys]
  have hxs : ∀ n, (histories p q n).evasions = historyPrefix x n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [evasion_prefix, ih, prefix_snoc, hxval]
  have ha : available e hp b y := by
    obtain ⟨N, hN⟩ := hav
    exact ⟨N, fun n hn => hN n hn (historyPrefix y n) (by simp [historyPrefix])⟩
  obtain ⟨N, hN⟩ := PredictionRobustProof.robustBoundedObservations e hp b y ha
  refine ⟨N, fun n hn => ?_⟩
  have hpred : prediction p q n = baseline (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) := by
    have hc := (PredictionSelfHistoryProof.actualHistoryCalibration (budgetRule b) q n).2
    change prediction p q n = budgetRule b (histories p q n).evasions
      (histories p q n).predictions at hc
    rw [hxs, hys] at hc
    simpa only [budgetRule, historyPrefix, List.length_ofFn] using hc
  change prediction p q n = evasion p q n
  rw [hpred]
  exact (hN n hn).trans (hxval n)

theorem ordinaryBaselineLearning : OrdinaryBaselineLearning := by
  intro b hb
  obtain ⟨_, p, hp, heq⟩ := baselineProgramRealization b hb
  refine ⟨p, hp, heq, fun e he hav => ?_⟩
  rw [heq]
  exact actualBaselineLearning b e he hav

end LogicLineages.ComputabilityKnowledge.PredictionBaselineGameProof
