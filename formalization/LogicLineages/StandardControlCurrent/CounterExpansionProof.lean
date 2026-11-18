module
public import LogicLineages.StandardControlCurrent.CounterExpansionCalibrationProof
public import LogicLineages.OrdinalComparison.CounterSourceTheoremProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CounterExpansionProof
open OrdinalComparison NumericalKernel CounterExpansion

theorem tail_affordable (n m c e t : Nat) (ht : CounterSourceTheorem.commonTail n m c e ≤ t) :
    c+2*(n+3)+1 ≤ t := by
  exact (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans ht))

theorem source : CounterExpansionTargets.CounterSource := by
  refine ⟨?_,CounterSourceTheorem.Proof.uniformTailPrograms⟩
  intro n m c e t u ht hu
  have hn := tail_affordable n m c e t ht
  have hm : e+2*(m+3)+1 ≤ u :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hu))
  have a := ladder n c t hn
  have b := ladder m e u hm
  have cn := (NumericalKernelProof.padded (n+3) c t (by omega) (by omega)).1
  have cm := (NumericalKernelProof.padded (m+3) e u (by omega) (by omega)).1
  change count (n+3) c t = CounterLeaderExpansion.count (n+3) c t at cn
  change count (m+3) e u = CounterLeaderExpansion.count (m+3) e u at cm
  have al := a.2.2.2.2.1
  have bl := b.2.2.2.2.1
  have ar := a.2.2.2.2.2
  have h := CounterSourceTheorem.Proof.wholeCounterLemma n m c e t u ht hu
  rcases h with ⟨ranks,ev,exp,lo,hi,mass,coll,ord,eq⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [a.2.1] using ranks
  · simpa only [al] using ev
  · simpa only [cn,al,ar] using exp
  · simpa only [cn,al] using lo
  · simpa only [cn,al] using hi
  · simpa only [al,bl] using mass
  · intro hmn hl
    have up := upper (n-m) m c t (by omega)
    rw [al,bl] at hl
    simpa only [cn,cm,up.2.1,up.2.2.1,up.2.2.2] using coll hmn hl
  · simpa only [cn,cm,al,bl] using ord
  · simpa only [cn,cm,al,bl] using eq

theorem full : CounterExpansionTargets.Full := ⟨ladder,upper,source⟩
end LogicLineages.StandardControlCurrent.CounterExpansionProof
