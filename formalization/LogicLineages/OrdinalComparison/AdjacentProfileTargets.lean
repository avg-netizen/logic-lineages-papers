module
public import LogicLineages.OrdinalComparison.AdjacentPackedDefinitions
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Full source paper07 thm:adjacent, lines523–536 and its genuine omega affine
base591–597. Every numerical mass is genuine; no order between c and e is
assumed. The proof's printed lower suffix norm B is calibrated as B−e/total B
in the separately gated packing chain; this statement is unchanged. -/
def ActualAdjacentProfileSeparation : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t c e : Nat, profileAdjacentThreshold L E ≤ t →
      c + actualOrdinalNorm L.1.repr ≤ t+1 → e + actualOrdinalNorm L.1.repr ≤ t →
      actualFixedLimitProfileEval E (actualSuffixKernel L.1.repr e t + actualSuffixKernelCount L.1.repr e t) <
        actualSuffixKernel L.1.repr c (t+1)

def ActualCrossMassProfileSeparation : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t u c e : Nat, profileAdjacentThreshold L E ≤ t → t < u →
      c + actualOrdinalNorm L.1.repr ≤ u → e + actualOrdinalNorm L.1.repr ≤ t →
      actualFixedLimitProfileEval E (actualSuffixKernel L.1.repr e t + actualSuffixKernelCount L.1.repr e t) <
        actualSuffixKernel L.1.repr c u

def ActualOmegaAffineCrossMassSeparation : Prop :=
  ∀ a b t u c e : Nat, max 4 (a+b+2) ≤ t → t < u → c+2 ≤ u → e+2 ≤ t →
    a*(actualSuffixKernel Ordinal.omega0 e t + actualSuffixKernelCount Ordinal.omega0 e t)+b <
      actualSuffixKernel Ordinal.omega0 c u

def FullActualCrossMassStrictInputSeparation : Prop :=
  ActualAdjacentProfileSeparation ∧ ActualCrossMassProfileSeparation ∧ ActualOmegaAffineCrossMassSeparation

end LogicLineages.OrdinalComparison.Targets
