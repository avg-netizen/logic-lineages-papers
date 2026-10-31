module
public import LogicLineages.OrdinalComparison.WWOriginalBoxControlTargets
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain

theorem originalBoxNumericalStep : Targets.OriginalBoxNumericalStep := by
  intro x s hs
  calc
    2 ^ x * s ≤ 2 ^ x * 2 ^ x := Nat.mul_le_mul_left _
      (hs.trans (Nat.lt_two_pow_self.le))
    _ = 2 ^ (2 * x) := by rw [Nat.two_mul, Nat.pow_add]
    _ ≤ 2 ^ (2 ^ x) := Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_pow (by decide : 2 ≠ 1) x)

theorem originalBoxControlEnvelope : Targets.OriginalBoxControlEnvelope := by
  intro s n hs
  by_cases hn : n = 0
  · subst n
    simpa using Nat.succ_le_of_lt (self_lt_fastControl 2 s)
  · have hseed : s + 1 ≤ s + 2 * n := by omega
    have hcount : 2 * n ≤ s + 2 * n + 1 := by omega
    have hfirst : (fastControl 0)^[2 * n] (s + 1) ≤ fastControl 1 (s + 2 * n) := by
      exact (((fastControl_strictMono 0).monotone.iterate (2 * n)) hseed).trans
        ((iterate_index_mono (fun x => (self_lt_fastControl 0 x).le) (s + 2 * n)) hcount)
    have hmid : s + 2 * n ≤ fastControl 1 (s + n) := by
      calc
        s + 2 * n ≤ 2 * (s + n) := by omega
        _ ≤ 2 ^ (s + n) := Nat.mul_le_pow (by decide : 2 ≠ 1) _
        _ ≤ fastControl 1 (s + n) := two_pow_le_fastControl 1 _
    have hlast : (fastControl 1)^[2] (s + n) ≤ fastControl 2 (s + n) :=
      (iterate_index_mono (fun x => (self_lt_fastControl 1 x).le) (s + n)) (by omega)
    exact hfirst.trans (((fastControl_strictMono 1).monotone hmid).trans hlast)

end LogicLineages.OrdinalComparison.Source.OriginalDomain
