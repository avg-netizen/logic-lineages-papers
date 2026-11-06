module
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.GapProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion

theorem sourceShiftedCounterPhiOrder : Targets.SourceShiftedCounterPhiOrder := by
  intro n c t v j k ht hv
  have hb := sourceCounterBounds n c (j.natAbs+k.natAbs) t ht
  have hu := CounterLeaderBounds.Proof.four_mul_lt_Phi (wordValue (leaderWord n c) t)
  have hg := CounterLeaderBounds.Proof.four_mul_lt_Phi v
  have hvK : j.natAbs+k.natAbs ≤ v := by unfold rangeTail at hv; omega
  have hjl : -(j.natAbs : Int) ≤ j := by cases j <;> simp <;> omega
  have hju : j ≤ (j.natAbs : Int) := Int.le_natAbs
  have hkl : -(k.natAbs : Int) ≤ k := by cases k <;> simp <;> omega
  have hku : k ≤ (k.natAbs : Int) := Int.le_natAbs
  have hpE : 0 < (sourceCount (n+3) c t : Int)+j := by omega
  have hpP : 0 < (Phi v : Int)+k := by omega
  have hgap := quantitativeCounterPhiGap n c (j.natAbs+k.natAbs) t v ht hv
  have hlo (h : wordValue (leaderWord n c) t ≤ v) :
      (sourceCount (n+3) c t : Int)+j < (Phi v : Int)+k := by
    have hh := hgap.1.mpr h
    omega
  have hhi (h : v < wordValue (leaderWord n c) t) :
      (Phi v : Int)+k < (sourceCount (n+3) c t : Int)+j := by
    have hh := hgap.2.mpr h
    omega
  refine ⟨hpE,hpP,?_,?_,?_,?_⟩
  · constructor
    · intro h
      by_contra hn
      have hh := hhi (by omega)
      exact (not_lt_of_ge hh.le) h
    · exact hlo
  · constructor
    · intro h
      rcases le_or_gt (wordValue (leaderWord n c) t) v with he | he
      · exact (ne_of_lt (hlo he)) h
      · exact (ne_of_gt (hhi he)) h
    · exact False.elim
  · constructor
    · intro h
      by_contra hn
      have hh := hhi (by omega)
      exact (not_lt_of_ge h) hh
    · intro h
      exact (hlo h).le
  · constructor
    · intro h
      by_contra hn
      have hh := hlo (by omega)
      exact (not_lt_of_ge hh.le) h
    · exact hhi

end LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.Proof
