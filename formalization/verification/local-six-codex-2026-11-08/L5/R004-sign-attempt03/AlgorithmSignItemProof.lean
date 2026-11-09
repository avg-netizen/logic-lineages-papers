module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmCollisionProof
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsStatementChecks

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion Algorithm
open KernelSourceCompletion

theorem rowSourceTail_source (r : Row) (a : Item) (ha : a ∈ active r) :
    sourceTail a ≤ rowSourceTail r := by
  exact (member_le_foldMax _ _ (List.mem_map.mpr ⟨a,ha,rfl⟩)).trans
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))

theorem signTail_source (r : Row) (a : Item) (ha : a ∈ active r) :
    sourceTail a ≤ signTail r :=
  (rowSourceTail_source r a ha).trans (Nat.le_max_left _ _)

theorem signTail_reach (r : Row) (a : Item) (ha : a ∈ active r) :
    reachTail (preimage a) (signPayment r) ≤ signTail r :=
  (member_le_foldMax _ _ (List.mem_map.mpr ⟨a,ha,rfl⟩)).trans (Nat.le_max_right _ _)

/-- The stage's leader is a literal Phi image at its emitted preimage.
All admission/domain information is proved at this current occurrence. -/
theorem preimage_facts (D : Nat) (r : Row) (a : Item) (hD : RowAllowed D r)
    (ha : a ∈ active (canonicalRow r)) (t : Nat) (ht : sourceTail a ≤ t) :
    WordAllowed D (preimage a) ∧ WordDomain (preimage a) t ∧
      wordValue (leader a).2 t = Phi (wordValue (preimage a) t) := by
  by_cases hc : isCounter a = true
  · have hp := counter_parameters D r a hD ha hc
    have hv := active_item_view D r a hD ha
    have hadm : WordAllowed D (preimage a) := by
      simp only [preimage,hc,if_true]
      exact allowed_word_append D _ _ hv.2.2.2
        (CounterWordGuardCompletion.Proof.leaderWord_allowed D _ _ (by omega))
    have he := RankedWordDecisionCompletion.Proof.exactSourceCounterExpansion D
      a.1 a.2.1 (innerWord a) (counterIndex a) (mass a) (by omega) hv.2.2.2
      (fun _ => t) ((counter_sourceTail_expansion a hc).trans ht)
    have hd := he.2.2.1 (a.1,a.2.1,leaderValueWord (innerWord a)
      (counterIndex a) (mass a)) (List.mem_cons_self)
    have hdom : WordDomain (preimage a) t := by
      have hd' : WordDomain ((innerWord a++leaderWord (counterIndex a) (mass a))++
          [phiLetter]) t := by simpa only [leaderValueWord,List.append_assoc] using hd
      have hprefix := (WordAlgebraProof.wordDomain_append _ _ _).mp hd'
      simpa only [preimage,hc,if_true] using hprefix.1
    refine ⟨hadm,hdom,?_⟩
    simp [leader,preimage,hc,leaderValueWord,WordAlgebraProof.wordValue_append,
      wordValue,letterValue,phiLetter]
  · have hf : isCounter a = false := Bool.eq_false_of_not_eq_true hc
    simpa [leader,hc] using ordinary_phi_preimage D r a hD ha hf t ht

theorem counter_preimage_value (D : Nat) (r : Row) (a : Item)
    (hD : RowAllowed D r) (ha : a ∈ active (canonicalRow r))
    (hc : isCounter a = true) (t : Nat) (ht : sourceTail a ≤ t) :
    wordValue (preimage a) t = CounterLeaderExpansion.leaderPreimage
      (counterIndex a) (mass a) (wordValue (innerWord a) t) := by
  simp only [preimage,hc,if_true,WordAlgebraProof.wordValue_append]
  exact CounterWordGuardCompletion.Proof.leaderWord_value _ _ _
    (counter_reached_leaderTail D r a hD ha hc t ht)

/-- The actual scheduled counter's doubled correction is nonnegative and
bounded by its actual leader preimage, rather than by a fraction of H. -/
theorem counter_correction_bound (D : Nat) (r : Row) (a : Item)
    (hD : RowAllowed D r) (ha : a ∈ active (canonicalRow r))
    (hc : isCounter a = true) (t : Nat) (ht : sourceTail a ≤ t) :
    0 ≤ 2*(wordValue a.2.2 t : Int)-(wordValue (leader a).2 t : Int) ∧
      2*(wordValue a.2.2 t : Int)-(wordValue (leader a).2 t : Int) ≤
        2*(wordValue (preimage a) t : Int)+2 := by
  have hv := active_item_view D r a hD ha
  have hreached := WordGuardCompletion.Proof.wordReachCorrect D (innerWord a)
    (CounterLeaderBounds.threshold (counterIndex a) (mass a)) t hv.2.2.2 (by
      simp only [sourceTail,hc,if_true] at ht
      exact ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans ht)
  let n := counterIndex a
  let c := mass a
  let u := wordValue (innerWord a) t
  have hsource : CounterLeaderExpansion.threshold n c ≤ u :=
    (Nat.le_max_left _ _).trans hreached.2
  have hi := CounterLeaderExpansion.Proof.exactCounterLeaderIdentity n c u hsource
  have hr := CounterLeaderBounds.Proof.actualResidualBounds.1 n c u
  have hp := CounterLeaderBounds.Proof.actualResidualBounds.2 n c u hreached.2
  have heven : (CounterLeaderExpansion.leader n c u : Int) =
      2*((CounterLeaderExpansion.leader n c u / 2 : Nat) : Int) := by
    obtain ⟨k,hk⟩ := hi.1
    omega
  rw [counter_count_value D r a hD ha hc t ht,
    counter_leader_value D r a hD ha hc t ht,counter_preimage_value D r a hD ha hc t ht]
  change 0 ≤ 2*(CounterLeaderExpansion.count (n+3) c u : Int)-
      (CounterLeaderExpansion.leader n c u : Int) ∧ _
  rw [hi.2.2,heven]
  constructor <;> omega

/-- Every current atom has cofinality at the literal sign payment and a
raw-input bound from its own actual preimage. Removed occurrences are absent
from this statement and cannot supply the maximum-variable provenance. -/
theorem current_preimage_provenance (D : Nat) (r : Row) (a : Item)
    (hD : RowAllowed D r) (ha : a ∈ active (canonicalRow r)) (t : Nat)
    (ht : signTail (canonicalRow r) ≤ t) :
    WordDomain (preimage a) t ∧ signPayment (canonicalRow r) ≤ wordValue (preimage a) t ∧
      t ≤ wordValue (preimage a) t + wordOffset (preimage a) ∧
      wordValue (leader a).2 t = Phi (wordValue (preimage a) t) := by
  have hs := (signTail_source _ a ha).trans ht
  have hp := preimage_facts D r a hD ha t hs
  have hreach := (signTail_reach _ a ha).trans ht
  have hc := WordGuardCompletion.Proof.wordReachCorrect D (preimage a)
    (signPayment (canonicalRow r)) t hp.1 hreach
  have ht' : wordTail (preimage a) ≤ t := by unfold reachTail at hreach; omega
  have hraw := (WordGuardCompletion.Proof.wordTailCorrect D (preimage a) t hp.1 ht').2
  exact ⟨hc.1,hc.2,hraw,hp.2.2⟩

theorem current_maximum_witness (maximum : Nat) (r : Row)
    (h : hasMaximum maximum (canonicalRow r) = true) :
    ∃ a ∈ active (canonicalRow r), a.1 ≠ 0 ∧ a.2.1 = maximum := by
  obtain ⟨a,ha,hname⟩ := List.any_eq_true.mp h
  exact ⟨a,ha,(canonical_item r a (List.mem_filter.mp ha).1).1,by simpa using hname⟩

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
