module
public import LogicLineages.OrdinalComparison.LimitPairCertificateDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ComparisonPrincipalNoteSource : Prop :=
  Primrec encodedComparisonPrincipalNote ∧ ∀ eta : NONote,
    (comparisonPrincipalNote eta).1.repr=Ordinal.omega0^eta.1.repr ∧
    encodedComparisonPrincipalNote (rawNoteEncode eta.1)=rawNoteEncode (comparisonPrincipalNote eta).1

/-- Complete same-limit-principal leaf of source section8's simultaneous
certificate. The profile modulus is genuinely uniformly computed. Every
integer input and mass is actual; strict comparison is characterized, then
its full requested lower-profile gap is proved. No separation oracle. -/
def ActualLimitPairCertificateProgram : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    encodedLimitPairCertificateTail p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  ∀ eta : NONote, Order.IsSuccLimit eta.1.repr → ∀ P : FixedLimitPositiveExpr,
    fixedLimitProfileBelow (Ordinal.omega0^eta.1.repr) P → ∀ c e t u : Nat,
    encodedLimitPairCertificateTail (rawNoteEncode eta.1) (positiveExprEncode P) c e≤t →
    encodedLimitPairCertificateTail (rawNoteEncode eta.1) (positiveExprEncode P) c e≤u →
      c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤u ∧
      e+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t ∧
      (actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t<
        actualSuffixKernel (Ordinal.omega0^eta.1.repr) c u ↔ t<u ∨ (t=u ∧ c<e)) ∧
      (actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t<
        actualSuffixKernel (Ordinal.omega0^eta.1.repr) c u →
          actualFixedLimitProfileEval P (actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t+
            actualSuffixKernelCount (Ordinal.omega0^eta.1.repr) e t)<
              actualSuffixKernel (Ordinal.omega0^eta.1.repr) c u)

end LogicLineages.OrdinalComparison.Targets
