module
public import LogicLineages.OrdinalComparison.AffineProfileCertificateDefinitions
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualAffineProfileSource : Prop :=
  Primrec₂ positiveAffineProfileCode ∧ ∀ a b : Nat,
    positiveAffineProfileCode a b=positiveExprEncode (positiveAffineProfile a b) ∧
    (∀ L : Ordinal.{0}, fixedLimitProfileBelow L (positiveAffineProfile a b)) ∧
    ∀ x : Nat, actualFixedLimitProfileEval (positiveAffineProfile a b) x=a*x+b

/-- Source section8 simultaneous-certificate CASE1, with its actual composed
profile, actual arbitrary open P argument, and a genuine uniform primitive
recursive numeric modulus. Stronger than the limit-exponent-only case; no
comparison/separation certificate is assumed. -/
def ActualAffineProfileCertificateProgram : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat × Nat =>
    encodedAffineProfileCertificateTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr=Ordinal.omega0^ell) →
    Ordinal.omega0<L.1.repr → ∀ P A : FixedLimitPositiveExpr,
    fixedLimitProfileBelow L.1.repr P → fixedLimitProfileBelow epsilonZero A → positiveExprHasInput A=true →
    ∀ c a b x : Nat,
    encodedAffineProfileCertificateTail (rawNoteEncode L.1) (positiveExprEncode P) c a b≤x →
      c+actualOrdinalNorm L.1.repr≤actualFixedLimitProfileEval A x ∧
      actualFixedLimitProfileEval P (a*x+b)<
        actualSuffixKernel L.1.repr c (actualFixedLimitProfileEval A x)

end LogicLineages.OrdinalComparison.Targets
