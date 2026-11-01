module
public import LogicLineages.OrdinalComparison.SignedKernelDomainDefinitions
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- An explicit common tail for the source block recurrence. The signed
child domain is still stated separately: at degree two negative offsets
cannot acquire a positive degree-one child depth. -/
def finiteKernelRecursionThreshold (d c : Nat) (j : Int) : Nat :=
  max (c + 2*d + 1) (c + 2*j.natAbs + 3)

/-- Literal source V, totalized only by Int.toNat outside positive depth. -/
def rawQuadraticShift (j : Int) (t : Nat) : Nat :=
  (Phi^[((Phi t / 2 : Nat) : Int) + j + 1 |>.toNat]) t

noncomputable def encodedFiniteKernelCount (d c t : Nat) : Nat :=
  encodedSuffixKernelCount (encodedNatNote d) c t

noncomputable def encodedFiniteKernelValue (d c t : Nat) : Nat :=
  encodedSuffixKernelValue (encodedNatNote d) c t

end LogicLineages.OrdinalComparison
