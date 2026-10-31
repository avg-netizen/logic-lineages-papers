module

public import LogicLineages.ComputabilityKnowledge.PredictionTapeGameTargets
public import LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeGameProof
open PredictionGame PredictionTapeObservation PredictionTapeBaseline PredictionTapeGame PredictionTapeGameTargets
open PredictionRobust (historyPrefix budgetPrefix)

theorem computableBudgetRule : ComputableBudgetRule := by
  intro b hb
  have harg : Computable (fun q : List Bool × List Bool => (budgetPrefix b q.1.length, q.1, q.2)) :=
    ((PredictionComputableBudgetProof.computableBudgetPrefix b hb).comp (Computable.list_length.comp Computable.fst)).pair
      (Computable.fst.pair Computable.snd)
  apply (PredictionTapeBaselineProof.primitiveRecursiveBaseline.to_comp.comp harg).of_eq
  intro q
  rfl

private theorem prefix_snoc {α : Type} (s : Nat → α) (n : Nat) :
    historyPrefix s (n + 1) = historyPrefix s n ++ [s n] := List.ofFn_succ_last

theorem actualAnyPredictorBaselineCorrect : ActualAnyPredictorBaselineCorrect := by
  intro b p e he hav
  let q := policy e he
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
  have ha : available e he b y := by
    obtain ⟨N, hN⟩ := hav
    exact ⟨N, fun n hn => hN n hn (historyPrefix y n) (by simp [historyPrefix])⟩
  obtain ⟨N, hN⟩ := PredictionTapeBaselineProof.robustBoundedObservations e he b y ha
  refine ⟨N, ?_⟩
  intro n hn
  change budgetRule b (histories p q n).evasions (histories p q n).predictions = evasion p q n
  rw [hxs, hys]
  simpa only [budgetRule, historyPrefix, List.length_ofFn, x, q] using (hN n hn).trans (hxval n)

end LogicLineages.ComputabilityKnowledge.PredictionTapeGameProof
