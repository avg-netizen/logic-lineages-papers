module
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.LeaderProof
public import LogicLineages.OrdinalComparison.CounterFixedShiftComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion
open CounterLeaderExpansion

theorem sourceShiftedCounterOrder : Targets.SourceShiftedCounterOrder := by
  intro n m c e t u j k ht hu
  have htf : CounterFixedShiftComparison.threshold n c e (j.natAbs+k.natAbs) ≤ t :=
    (Nat.le_max_left _ _).trans ht
  have huf : CounterFixedShiftComparison.threshold m e c (k.natAbs+j.natAbs) ≤ u :=
    (Nat.le_max_left _ _).trans hu
  have htb : c+(n+3)+1 ≤ t := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht)
  have hub : e+(m+3)+1 ≤ u := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hu)
  have htl : leaderTail n c ≤ t := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans ht)
  have hul : leaderTail m e ≤ u := (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hu)
  have hb := Focused.sourceProcessBridge (n+3) c t (by omega) htb
  have hb' := Focused.sourceProcessBridge (m+3) e u (by omega) hub
  have hs := CounterFixedShiftComparison.Proof.actualFixedShiftComparison n m c e t u j k
    htf (by simpa [Nat.add_comm] using huf)
  have htc : CounterLeaderComparison.threshold n c e ≤ t := (Nat.le_max_left _ _).trans htf
  have huc : CounterLeaderComparison.threshold m e c ≤ u := (Nat.le_max_left _ _).trans huf
  have ho := CounterLeaderComparison.Proof.actualCounterStrictOrder n m c e t u htc huc
  have he := (CounterLeaderComparison.Proof.actualCounterEquality n m c e t u htc huc).1
  have hlt : leader n c t < leader m e u ↔ leaderPreimage n c t < leaderPreimage m e u :=
    Phi_strictMono.lt_iff_lt
  have heq : leader n c t = leader m e u ↔ leaderPreimage n c t = leaderPreimage m e u :=
    Phi_strictMono.injective.eq_iff
  rw [hb.1,hb'.1]
  change 0 < (count (n+3) c t : Int)+j ∧ 0 < (count (m+3) e u : Int)+k ∧ _
  refine ⟨hs.1,hs.2.1,?_,?_⟩
  · change ((count (n+3) c t : Int)+j < (count (m+3) e u : Int)+k ↔
      CounterLexLT n m j k (wordValue (leaderWord n c) t) (wordValue (leaderWord m e) u))
    rw [hs.2.2.1, ho, he, hlt, heq, leaderWord_value n c t htl,
      leaderWord_value m e u hul]
    simp only [CounterLexLT]
    constructor
    · rintro (h | h)
      · rcases h with h | ⟨he,hlt⟩
        · exact Or.inl h
        · exact Or.inr ⟨he,Or.inl hlt⟩
      · exact Or.inr ⟨h.1.1,Or.inr ⟨h.1.2,h.2⟩⟩
    · rintro (h | ⟨he,h⟩)
      · exact Or.inl (Or.inl h)
      · rcases h with h | ⟨hn,hj⟩
        · exact Or.inl (Or.inr ⟨he,h⟩)
        · exact Or.inr ⟨⟨he,hn⟩,hj⟩
  · change ((count (n+3) c t : Int)+j = (count (m+3) e u : Int)+k ↔
      wordValue (leaderWord n c) t = wordValue (leaderWord m e) u ∧ n = m ∧ j = k)
    rw [hs.2.2.2,he,heq,leaderWord_value n c t htl,leaderWord_value m e u hul]
    exact and_assoc

end LogicLineages.OrdinalComparison.CounterWordGuardCompletion.Proof
