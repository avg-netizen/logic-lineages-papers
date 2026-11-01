module
public import LogicLineages.OrdinalComparison.KernelInputProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def PrincipalKernelInputProgramPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat × Nat =>
    encodedPrincipalKernelInputCompare p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- Every strict input inequality survives arbitrary literal masses, on a
single explicitly computed source tail. No eventual child-comparison or
strict-order-preservation oracle is supplied. -/
def ActualPrincipalKernelStrictInputs : Prop :=
  ∀ eta : NONote, 0<eta.1.repr → ∀ c e t u : Nat,
    encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤t →
    encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤u → t<u →
    actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t<
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) e u

/-- Whole same-principal source RR numeric-input rule, including genuine
uniform primitive recursion, both actual domains and every order case.
This does not claim completion of mixed-principal/sign recursion. -/
def ActualPrincipalKernelInputProgram : Prop :=
  PrincipalKernelInputProgramPrimitiveRecursive ∧
  ∀ eta : NONote, 0<eta.1.repr → ∀ c e t u : Nat,
    encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤t →
    encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤u →
    c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t ∧
    e+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤u ∧
    (encodedPrincipalKernelInputCompare (rawNoteEncode eta.1) c e t u=0 ↔
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t<actualSuffixKernel (Ordinal.omega0^eta.1.repr) e u) ∧
    (encodedPrincipalKernelInputCompare (rawNoteEncode eta.1) c e t u=1 ↔
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t=actualSuffixKernel (Ordinal.omega0^eta.1.repr) e u) ∧
    (encodedPrincipalKernelInputCompare (rawNoteEncode eta.1) c e t u=2 ↔
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) e u<actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t)

end LogicLineages.OrdinalComparison.Targets
