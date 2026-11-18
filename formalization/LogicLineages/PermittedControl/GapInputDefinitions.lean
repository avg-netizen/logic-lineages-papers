module
public import LogicLineages.PermittedControl.RelativeDescentDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Positive source profile bound, including the zero-target strictness unit. -/
noncomputable def gapProfileBound (mu nu : Ordinal.{0}) : Nat :=
  max 1 (max (actualOrdinalNorm mu) (actualOrdinalNorm nu))

/-- Explicit effective tail proposed for all three source clauses; k=0 for
(i),(ii), and the source reserve enlargement 2k for (iii). -/
noncomputable def gapInputTail (lam mu lam' mu' : Ordinal.{0}) (k : Nat) : Nat :=
  2 + actualOrdinalNorm lam + actualOrdinalNorm lam' + gapProfileBound mu mu' + 2*k

/-- Total finite-code implementation of the same explicit tail. Input order:
(lambdaP, muP, lambdaQ, muQ, k), with right-nested pairing. -/
def encodedGapInputTail (z : Nat × Nat × Nat × Nat × Nat) : Nat :=
  2 + rawNormCode z.1 + rawNormCode z.2.2.1 +
    max 1 (max (rawNormCode z.2.1) (rawNormCode z.2.2.2.1)) + 2*z.2.2.2.2

end LogicLineages.PermittedControl
