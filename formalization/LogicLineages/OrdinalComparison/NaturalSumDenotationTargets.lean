module
public import LogicLineages.OrdinalComparison.NaturalSumTargets
public import Mathlib.SetTheory.Ordinal.CantorNormalForm

@[expose] public section

/-! The external ordinal-denotation gate for natural sum. The raw syntactic
coefficient specification is an intermediate algorithm invariant; acceptance
of the paper's natural-sum claim additionally requires this genuine Mathlib
Cantor-normal-form coefficient statement for every actual ordinal exponent. -/

namespace LogicLineages.OrdinalComparison.Targets

def NaturalSumOrdinalCoefficients (add : NONote → NONote → NONote) : Prop :=
  ∀ (a b : NONote) (q : Ordinal),
    Ordinal.CNF.coeff Ordinal.omega0 (add a b).1.repr q =
      Ordinal.CNF.coeff Ordinal.omega0 a.1.repr q +
      Ordinal.CNF.coeff Ordinal.omega0 b.1.repr q

end LogicLineages.OrdinalComparison.Targets
