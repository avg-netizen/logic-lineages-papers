module
public import LogicLineages.OrdinalComparison.CounterFixedShiftComparisonGapProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterFixedShiftComparison.Proof
open CounterLeaderExpansion

private theorem positive_shift (n c e K t : Nat) (j : Int)
    (ht : CounterFixedShiftComparison.threshold n c e K ≤ t) (hj : j.natAbs ≤ K) :
    0 < (count (n+3) c t : Int)+j := by
  have htc : CounterLeaderComparison.threshold n c e ≤ t := (Nat.le_max_left _ _).trans ht
  have htb : CounterLeaderBounds.threshold n c ≤ t := (Nat.le_max_left _ _).trans htc
  have h4 : 4*K ≤ t := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht)
  have hl := input_lt_leader n c t
  have hb := (CounterLeaderBounds.Proof.strictActualLeaderBounds n c t htb).1
  have hjl : -(j.natAbs : Int) ≤ j := by omega
  omega

theorem actualFixedShiftComparison : Targets.ActualFixedShiftComparison := by
  intro n m c e t u j l ht hu
  have hjl : -(j.natAbs : Int) ≤ j := by omega
  have hju : j ≤ (j.natAbs : Int) := Int.le_natAbs
  have hll : -(l.natAbs : Int) ≤ l := by omega
  have hlu : l ≤ (l.natAbs : Int) := Int.le_natAbs
  refine ⟨positive_shift n c e _ t j ht (by omega),
    positive_shift m e c _ u l hu (by omega),?_⟩
  rcases lt_trichotomy (count (n+3) c t) (count (m+3) e u) with hc | hc | hc
  · have hg := actualQuantitativeCounterGap n m c e (j.natAbs+l.natAbs) t u ht hu hc
    constructor <;> omega
  · constructor <;> omega
  · have hg := actualQuantitativeCounterGap m n e c (j.natAbs+l.natAbs) u t hu ht hc
    constructor <;> omega

end LogicLineages.OrdinalComparison.CounterFixedShiftComparison.Proof
