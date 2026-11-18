module
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionDefinitions
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions
public import LogicLineages.OrdinalComparison.EncodedMaximumDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NumericalKernel
open OrdinalComparison
noncomputable def first (d c t : Nat) : Ordinal :=
  actualMaximumPredecessor (Ordinal.omega0 ^ (d : Ordinal)) (Phi t - c)
noncomputable def count (d c t : Nat) : Nat :=
  1 + actualControlledCount (compensatedPrefixControl c) (first d c t)
noncomputable def value (d c t : Nat) : Nat := (Phi^[count d c t]) t
noncomputable def state (d c t i : Nat) : Ordinal :=
  if i=0 then Ordinal.omega0 ^ (d : Ordinal)
  else actualControlledStateAfter (compensatedPrefixControl c) (first d c t) (i-1)
noncomputable def depth (d c : Nat) (j : Int) (t : Nat) : Int := (count d c t : Int)+j
noncomputable def signed (d c : Nat) (j : Int) (t : Nat) : Nat :=
  (Phi^[(depth d c j t).toNat]) t
noncomputable def countCode (d c t : Nat) : Nat :=
  1 + encodedCompensatedCountValue c
    (encodedMaximumPredecessor (encodedNodeCode (encodedNatNote d) 0 0) (Phi t-c))
noncomputable def valueCode (d c t : Nat) : Nat := (Phi^[countCode d c t]) t
end LogicLineages.StandardControlCurrent.NumericalKernel
