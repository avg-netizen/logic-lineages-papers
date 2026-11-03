module
public import LogicLineages.OrdinalComparison.CounterLeaderComparisonOrderProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderComparison.Proof
open CounterLeaderExpansion

theorem actualCounterEquality : Targets.ActualCounterEquality := by
  intro n m c e t u ht hu
  have hf := actualCounterStrictOrder n m c e t u ht hu
  have hr := actualCounterStrictOrder m n e c u t hu ht
  have heq : count (n+3) c t = count (m+3) e u ↔ leader n c t = leader m e u ∧ n = m := by
    constructor
    · intro hc
      have ha : ¬ leader n c t < leader m e u := by
        intro h
        have := hf.mpr (Or.inl h)
        omega
      have hb : ¬ leader m e u < leader n c t := by
        intro h
        have := hr.mpr (Or.inl h)
        omega
      have hh : leader n c t = leader m e u := by omega
      have hna : ¬ n < m := by
        intro h
        have := hf.mpr (Or.inr ⟨hh,h⟩)
        omega
      have hnb : ¬ m < n := by
        intro h
        have := hr.mpr (Or.inr ⟨hh.symm,h⟩)
        omega
      exact ⟨hh,by omega⟩
    · rintro ⟨hh,rfl⟩
      exact (SameRankLeaderRecognition.Proof.actualSameRankRecognition n c e t u
        ((Nat.le_max_right _ _).trans ht) ((Nat.le_max_right _ _).trans hu)).2 hh
  refine ⟨heq,?_⟩
  constructor
  · intro hc
    obtain ⟨hh,hn⟩ := heq.mp hc
    subst m
    have h := (SameRankLeaderRecognition.Proof.actualSameRankRecognition n c e t u
      ((Nat.le_max_right _ _).trans ht) ((Nat.le_max_right _ _).trans hu)).1.mp hh
    exact ⟨rfl,h⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

end LogicLineages.OrdinalComparison.CounterLeaderComparison.Proof
