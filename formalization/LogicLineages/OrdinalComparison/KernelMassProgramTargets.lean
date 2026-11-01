module
public import LogicLineages.OrdinalComparison.KernelMassProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualStrictMassSyntaxBound : Prop :=
  ∀ eta : NONote, actualStrictMassThreshold eta≤10+2*Vendor.R1.treeWeight eta.1

def PrincipalKernelMassProgramPrimitiveRecursive : Prop :=
  Primrec₂ encodedPrincipalKernelMassKey ∧ Primrec encodedStrictMassSyntaxBound ∧
  Primrec (fun p : Nat × Nat × Nat => encodedPrincipalKernelMassModulus p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat => encodedPrincipalKernelMassCompare p.1 p.2.1 p.2.2)

def PrincipalKernelMassProgramSource : Prop :=
  ∀ (eta : NONote) (c e : Nat),
    encodedPrincipalKernelMassKey (rawNoteEncode eta.1) c=principalKernelMassKey eta c ∧
    principalKernelMassModulus eta c e≤encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e ∧
    orderingCode (principalKernelMassCompare eta c e)=encodedPrincipalKernelMassCompare (rawNoteEncode eta.1) c e

/-- Actual RR equal-input source rule with an EXPLICIT UNIFORM numeric
compiler and a computed genuine-domain tail. This is a paid comparison rule,
not an assertion that the full recursive two-sort algorithm is complete. -/
def ActualPrincipalKernelMassProgram : Prop :=
  PrincipalKernelMassProgramPrimitiveRecursive ∧
  ∀ eta : NONote, 0<eta.1.repr → ∀ (c e t : Nat),
    encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c e≤t →
      c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t ∧
      e+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t ∧
      (encodedPrincipalKernelMassCompare (rawNoteEncode eta.1) c e=0 ↔
        actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t<actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t) ∧
      (encodedPrincipalKernelMassCompare (rawNoteEncode eta.1) c e=1 ↔
        actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t=actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t) ∧
      (encodedPrincipalKernelMassCompare (rawNoteEncode eta.1) c e=2 ↔
        actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t<actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t)

end LogicLineages.OrdinalComparison.Targets
