module
public import LogicLineages.OrdinalComparison.Definitions
public import Mathlib.SetTheory.Ordinal.CantorNormalForm

@[expose] public section

/-! Source definitions of actual natural ordinal arithmetic. Natural sum
collects equal Cantor coefficients. Natural product expands pairs of monomials,
naturally adds their exponents, multiplies their finite coefficients, and then
collects the resulting monomials. These definitions concern actual Ordinal
values and do not refer to either notation algorithm.
-/

namespace LogicLineages.OrdinalComparison

noncomputable def ordinalNaturalSum (a b : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.CNF.eval Ordinal.omega0
    (Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b)

noncomputable def ordinalNaturalProduct (a b : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.CNF.eval Ordinal.omega0
    ((Ordinal.CNF Ordinal.omega0 a).foldr
      (fun p acc => (Ordinal.CNF Ordinal.omega0 b).foldr
        (fun q rest => Finsupp.single (ordinalNaturalSum p.1 q.1) (p.2 * q.2) + rest)
        acc) 0)

end LogicLineages.OrdinalComparison
