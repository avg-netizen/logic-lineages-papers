module
public import LogicLineages.OrdinalComparison.StrictMassThresholdDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal same-input key of paper07 section8: mass is ignored at omega,
ceil(mass/2) at omega squared, and mass itself at higher principals. -/
def principalKernelMassKey (eta : NONote) (c : Nat) : Nat :=
  if eta.1=ONote.ofNat 1 then 0 else if eta.1=ONote.ofNat 2 then (c+1)/2 else c

/-- Executable genuine-input/eventual-order modulus on faithful notation. -/
def principalKernelMassModulus (eta : NONote) (c e : Nat) : Nat :=
  max 1 (max (actualStrictMassThreshold eta) (max c e+1+Vendor.R1.treeWeight eta.1))

/-- Reverse-key scalar comparison, with no kernel evaluation in the compiler. -/
def principalKernelMassCompare (eta : NONote) (c e : Nat) : Ordering :=
  if principalKernelMassKey eta e < principalKernelMassKey eta c then .lt
  else if principalKernelMassKey eta c < principalKernelMassKey eta e then .gt else .eq

end LogicLineages.OrdinalComparison
