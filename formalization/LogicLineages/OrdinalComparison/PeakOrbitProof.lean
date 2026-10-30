module
public import LogicLineages.OrdinalComparison.PeakOrbitTargets
public import LogicLineages.OrdinalComparison.ActualTerminal
public import LogicLineages.OrdinalComparison.ElementaryControl

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem phi_iteration_increases (t k : Nat) : t + k ≤ (Phi^[k]) t := by
  induction k with
  | zero => simp only [Nat.add_zero, Function.iterate_zero_apply, le_refl]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := self_lt_Phi ((Phi^[k]) t)
    omega

theorem actualSparsePeaks : Targets.ActualSparsePeaks := by
  intro a ha hinfinite hnorm
  dsimp only
  let L := actualReplacementCount a
  let s := (Phi^[L - 1]) (actualOrdinalNorm a)
  let Z := actualTerminalValue a
  have hcount := congrArg (fun p : Nat × Nat => p.2) ((actualTerminalRecursion a ha).2 hinfinite)
  change L = actualReplacementCount (actualDescentStep a) + 1 at hcount
  have hpos : 0 < L := by omega
  have htime : actualOrdinalNorm a + (L - 1) ≤ s := phi_iteration_increases _ _
  have hLs : L ≤ s - 1 := by omega
  have hident := (actualTerminalValueIdentities a ha).2
  have hpeak : Z = Phi s := by
    have hL : L = L - 1 + 1 := by omega
    change Z = (Phi^[L]) (actualOrdinalNorm a) at hident
    rw [hL, Function.iterate_succ_apply'] at hident
    exact hident
  have hvalue : actualCollapse a = Z + L := (actualTerminalValueIdentities a ha).1
  have hsmall : L < Z := by
    have h := self_lt_Phi s
    rw [← hpeak] at h
    omega
  refine ⟨hpos, hLs, hpeak, ?_, hvalue, ?_, ?_, ?_⟩
  · omega
  · omega
  · change 2 * Z < Phi (s + 1)
    rw [hpeak]
    have h := Phi_linear_gap s
    omega
  · intro u hu
    exact Phi_strictMono.monotone (by omega)

theorem controlRootOrbitCancellation : Targets.ControlRootOrbitCancellation := by
  intro t u L J ht hu heq
  induction L generalizing J with
  | zero =>
    cases J with
    | zero =>
      exact ⟨rfl, by simpa only [Function.iterate_zero_apply] using heq⟩
    | succ J =>
      apply False.elim
      apply ht
      refine ⟨(Phi^[J]) u, ?_⟩
      simpa only [Function.iterate_zero_apply, Function.iterate_succ_apply'] using heq.symm
  | succ L ih =>
    cases J with
    | zero =>
      apply False.elim
      apply hu
      refine ⟨(Phi^[L]) t, ?_⟩
      simpa only [Function.iterate_zero_apply, Function.iterate_succ_apply'] using heq
    | succ J =>
      have hcancel : (Phi^[L]) t = (Phi^[J]) u :=
        Phi_strictMono.injective (by simpa only [Function.iterate_succ_apply'] using heq)
      have h := ih J hcancel
      exact ⟨congrArg Nat.succ h.1, h.2⟩

theorem actualRootPeakInjectivity : Targets.ActualRootPeakInjectivity := by
  intro a b ha hb _ _ hroota hrootb hpeak
  have hia := actualTerminalValueIdentities a ha
  have hib := actualTerminalValueIdentities b hb
  have horbit : (Phi^[actualReplacementCount a]) (actualOrdinalNorm a) =
      (Phi^[actualReplacementCount b]) (actualOrdinalNorm b) := hia.2.symm.trans (hpeak.trans hib.2)
  have hcancel := controlRootOrbitCancellation _ _ _ _ hroota hrootb horbit
  have hnorm : actualOrdinalNorm a = actualOrdinalNorm b := hcancel.2
  have hvalues : actualCollapse a = actualCollapse b := by rw [hia.1, hib.1, hpeak, hcancel.1]
  apply le_antisymm
  · by_contra hn
    have hba : b < a := lt_of_not_ge hn
    have hbudget : actualOrdinalNorm b ≤ Phi (actualOrdinalNorm a) := by
      rw [← hnorm]
      exact (self_lt_Phi _).le
    have hstrict := actualCollapse_controlledStrictness a ha b hba hbudget
    omega
  · by_contra hn
    have hab : a < b := lt_of_not_ge hn
    have hbudget : actualOrdinalNorm a ≤ Phi (actualOrdinalNorm b) := by
      rw [hnorm]
      exact (self_lt_Phi _).le
    have hstrict := actualCollapse_controlledStrictness b hb a hab hbudget
    omega

end LogicLineages.OrdinalComparison
