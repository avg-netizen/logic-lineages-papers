module
public import LogicLineages.OrdinalComparison.KernelCounterResidueDefinitions
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionDefinitions
public import LogicLineages.OrdinalComparison.CounterSourceTheoremDefinitions
public import LogicLineages.OrdinalComparison.ScheduledCountDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion

/-- PROPOSED corrected paper08 convention: original external schedule, with
entry zero the first replacement budget. No current-state norm is substituted. -/
def sourceBudget (c t i : Nat) : Nat := (Phi^[i+1]) t - c

/-- Independently evaluated first-finite count, starting at the unpadded
principal suffix and using the limit-part predecessor. The old printed
whole-current-state process is a different, preserved definition. -/
noncomputable def sourceCount (d c t : Nat) : Nat :=
  actualScheduledCount (sourceBudget c t) (Ordinal.omega0 ^ (d : Ordinal))

noncomputable def sourceValue (d c t : Nat) : Nat := (Phi^[sourceCount d c t]) t

noncomputable def sourceState (d c t i : Nat) : Ordinal :=
  actualScheduledStateAfter (sourceBudget c t) (Ordinal.omega0 ^ (d : Ordinal)) i

/-- This is a proposed SOURCE domain correction, never a total extension of
negative degree-one depths. -/
def admissibleSignedPair (d : Nat) (j : Int) : Prop :=
  2 ≤ d ∨ (d = 1 ∧ 0 ≤ j)

def residueTail (d c : Nat) (j : Int) (m : Nat) : Nat :=
  max (correctedSignedKernelThreshold d c j m) (kernelCounterThreshold d c m)

end LogicLineages.OrdinalComparison.KernelSourceCompletion
