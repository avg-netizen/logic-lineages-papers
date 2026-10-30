module

public import LogicLineages.ComputabilityKnowledge.PredictionFlipMaskTargets
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeProof
public import LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderProof
public import LogicLineages.ComputabilityKnowledge.PredictionComputableBudgetProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFlipMaskProof
open PredictionGame PredictionFiniteChange PredictionCodeEvader PredictionFlipMask PredictionBaselineGame
open PredictionFlipMaskTargets

theorem flipEventComputable : FlipEventComputable := by
  intro R hR
  have hc : Computable (fun q : Nat × List Bool => completedCode q.2) :=
    PredictionCodeEvaderProof.completedCodePrimitiveRecursive.to_comp.comp Computable.snd
  have ha : Computable (fun q : (Nat × List Bool) × Nat => (q.1.1, q.2, q.1.2.length)) :=
    (Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair (Computable.list_length.comp (Computable.snd.comp Computable.fst)))
  have he : Computable₂ (fun q : Nat × List Bool => fun k : Nat => changeEvent R q.1 k q.2.length) := by
    apply ((PredictionFiniteChangeProof.finiteChangeComputable R hR).2.comp ha).of_eq
    intro q
    dsimp only
  apply (Computable.option_casesOn hc (Computable.const false) he).of_eq
  intro q
  unfold flipEvent
  cases completedCode q.2 <;> rfl

theorem finiteActualFlipMask : FiniteActualFlipMask := by
  classical
  intro R z hfin p e
  rcases PredictionCodeEvaderProof.completedCodeActualStabilization p e with hnone | ⟨N, k, hcode⟩
  · exact ⟨0, fun n _ => by simp only [flipEvent, hnone n]⟩
  · let L := (hfin k).toFinset.sup id
    have hbound : ∀ n : Nat, n ∈ changeSet R z k → n ≤ L := by
      intro n hn
      exact Finset.le_sup (f := id) ((hfin k).mem_toFinset.mpr hn)
    refine ⟨max N (L + 1), ?_⟩
    intro n hn
    have hNn : N ≤ n := (Nat.le_max_left _ _).trans hn
    have hLn : L < n := by have := (Nat.le_max_right N (L + 1)).trans hn; omega
    have hevent : changeEvent R z k n = false := by
      cases he : changeEvent R z k n with
      | false => rfl
      | true => have hb := hbound n he; omega
    simpa only [flipEvent, hcode n hNn, (history_lengths p e n).1] using hevent

theorem infiniteCodeFlipMask : InfiniteCodeFlipMask := by
  intro R z k hinf p N
  obtain ⟨n, hn, hnot⟩ := hinf.exists_notMem_finset (Finset.range (max N (k + 1)))
  have hlarge : max N (k + 1) ≤ n := by simpa only [Finset.mem_range, not_lt] using hnot
  have hN : N ≤ n := (Nat.le_max_left _ _).trans hlarge
  have hk : k < n := by have := (Nat.le_max_right N (k + 1)).trans hlarge; omega
  have hc := (PredictionCodeEvaderProof.codeEvaderStream k p n).2
  rw [if_pos hk] at hc
  refine ⟨n, hN, ?_⟩
  change changeEvent R z k n = true at hn
  simpa only [flipEvent, hc, (history_lengths p (codePolicy k) n).1] using hn

theorem flipRuleComputable : FlipRuleComputable := by
  intro R b hR hb
  have he : Computable (fun q : Nat × List Bool × List Bool => flipEvent R q.1 q.2.1) := by
    apply ((flipEventComputable R hR).comp (Computable.fst.pair (Computable.fst.comp Computable.snd))).of_eq
    intro q
    dsimp only
  have hbase : Computable (fun q : Nat × List Bool × List Bool => budgetRule b q.2.1 q.2.2) :=
    (PredictionComputableBudgetProof.computableBudgetRule b hb).comp
      (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)
  have hnot := (Primrec.dom_bool Bool.not).to_comp.comp hbase
  apply (Computable.cond he hnot hbase).of_eq
  intro q
  unfold flipRule
  cases flipEvent R q.1 q.2.1 <;> rfl

end LogicLineages.ComputabilityKnowledge.PredictionFlipMaskProof
