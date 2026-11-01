module
public import LogicLineages.OrdinalComparison.KernelProfileLeafDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Actual source two-sort growth, including arbitrary nonempty kernel words;
this discharges argument growth rather than adding it as a global oracle. -/
def ActualOpenComparisonSourceGrowth : Prop :=
  ∀ A : OneVariableComparisonExpr, oneVariableComparisonValid A → oneVariableComparisonOpen A →
    ∀ x : Nat, oneVariableComparisonDomainBound A≤x →
      oneVariableComparisonDomainAt A x ∧ x≤actualOneVariableComparisonValue A x

/-- Literal numerical bounded-argument leaf used by source certificate CASE5.
Every source argument s<=t is absorbed; the modulus is genuinely uniform PR. -/
def ActualBoundedKernelProfileLeafProgram : Prop :=
  Primrec (fun p : Nat × Nat × Nat => encodedKernelProfileLeafTail p.1 p.2.1 p.2.2) ∧
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr=Ordinal.omega0^ell) →
    Ordinal.omega0<L.1.repr → ∀ P : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr P →
    ∀ c t : Nat, encodedKernelProfileLeafTail (rawNoteEncode L.1) (positiveExprEncode P) c≤t →
      c+actualOrdinalNorm L.1.repr≤t ∧ ∀ s : Nat, s≤t →
        actualFixedLimitProfileEval P s<actualSuffixKernel L.1.repr c t

/-- Entire source affine certificate leaf for ANY genuine inner P/R value,
not just when that inner argument happens to be an original P1 tree. -/
def ActualAffineKernelIntegerInputsProgram : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat × Nat =>
    encodedAffineProfileCertificateTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr=Ordinal.omega0^ell) →
    Ordinal.omega0<L.1.repr → ∀ P : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr P →
    ∀ c a b x t : Nat,
    encodedAffineProfileCertificateTail (rawNoteEncode L.1) (positiveExprEncode P) c a b≤x → x≤t →
      c+actualOrdinalNorm L.1.repr≤t ∧
      actualFixedLimitProfileEval P (a*x+b)<actualSuffixKernel L.1.repr c t

end LogicLineages.OrdinalComparison.Targets
