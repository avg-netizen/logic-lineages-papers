module

public import LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetTargets
public import LogicLineages.ComputabilityKnowledge.PredictionRobustProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetProof
open PredictionGame PredictionLearning PredictionRobust PredictionBaselineGame PredictionComputableBudgetTargets

theorem computableBudgetPrefix : ComputableBudgetPrefix := by
  intro b hb
  have hs : Computable₂ (fun _ : Nat => fun v : Nat × List Nat => v.2 ++ [b v.1]) :=
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hb.comp (Computable.fst.comp Computable.snd))).to₂
  have hrec := Computable.nat_rec Computable.id (Computable.const ([] : List Nat)) hs
  have heq : ∀ n : Nat, Nat.rec (motive := fun _ => List Nat) [] (fun i prev => prev ++ [b i]) n = historyPrefix b n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.rec [] (fun i prev => prev ++ [b i]) n ++ [b n] = _
      rw [ih]
      simpa only [historyPrefix, Fin.val_castSucc, Fin.val_last] using (List.ofFn_succ_last (f := fun i : Fin (n + 1) => b i)).symm
  apply (hrec.comp Computable.succ).of_eq
  intro n
  exact heq (n + 1)

theorem computableBudgetRule : ComputableBudgetRule := by
  intro b hb
  have harg : Computable (fun q : List Bool × List Bool => (budgetPrefix b q.1.length, q.1, q.2)) :=
    ((computableBudgetPrefix b hb).comp (Computable.list_length.comp Computable.fst)).pair
      (Computable.fst.pair Computable.snd)
  apply (PredictionRobustProof.primitiveRecursiveBaseline.to_comp.comp harg).of_eq
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
  obtain ⟨N, hN⟩ := PredictionRobustProof.robustBoundedObservations e he b y ha
  refine ⟨N, ?_⟩
  intro n hn
  change budgetRule b (histories p q n).evasions (histories p q n).predictions = evasion p q n
  rw [hxs, hys]
  simpa only [budgetRule, historyPrefix, List.length_ofFn, x, q] using (hN n hn).trans (hxval n)

end LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetProof
