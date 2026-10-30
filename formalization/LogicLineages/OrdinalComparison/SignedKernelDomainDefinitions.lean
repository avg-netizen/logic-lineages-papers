module

public import LogicLineages.OrdinalComparison.KernelCounterResidueDefinitions
public import Mathlib.Data.Int.Basic

@[expose] public section
namespace LogicLineages.OrdinalComparison

noncomputable def signedKernelDepth (d c : Nat) (j : Int) (t : Nat) : Int :=
  (actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t : Int) + j

/-- Raw total extension only. It represents the source signed X exclusively on
its genuine domain `0 < signedKernelDepth d c j t`. Values at nonpositive depth
are not asserted to have source meaning or eventual constant residues. -/
noncomputable def rawSignedKernelValue (d c : Nat) (j : Int) (t : Nat) : Nat :=
  (Phi^[(signedKernelDepth d c j t).toNat]) t

def correctedSignedKernelThreshold (d c : Nat) (j : Int) (m : Nat) : Nat :=
  max m (max (c + d + 1) (c + 2 * j.natAbs + 3))

end LogicLineages.OrdinalComparison
