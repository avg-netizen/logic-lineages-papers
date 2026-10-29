module
public import LogicLineages.OrdinalComparison.NaturalArithmeticTargets
public import LogicLineages.OrdinalComparison.NaturalSumDenotation

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem naturalSumDenotation : Targets.NaturalSumDenotation naturalSum := by
  intro a b
  have hcoeff : Ordinal.CNF.coeff Ordinal.omega0 (naturalSum a b).1.repr =
      Ordinal.CNF.coeff Ordinal.omega0 a.1.repr +
        Ordinal.CNF.coeff Ordinal.omega0 b.1.repr := by
    apply Finsupp.ext
    intro q
    exact naturalSumOrdinalCoefficients a b q
  calc
    (naturalSum a b).1.repr = Ordinal.CNF.eval Ordinal.omega0
        (Ordinal.CNF.coeff Ordinal.omega0 (naturalSum a b).1.repr) :=
      (Ordinal.CNF.eval_coeff _ _).symm
    _ = ordinalNaturalSum a.1.repr b.1.repr := by
      rw [hcoeff]
      rfl

end LogicLineages.OrdinalComparison
