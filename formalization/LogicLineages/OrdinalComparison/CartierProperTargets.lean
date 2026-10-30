module
public import LogicLineages.OrdinalComparison.CartierProperDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual no-polynomial-part suppliers for source lem:poles. No partial
fraction expansion or properness preservation is supplied as an oracle. -/
def ActualRationalProperDegree : Prop :=
  ∀ (K : Type u) [Field K], ∀ f : RatFunc K,
    actualRationalProper f ↔ f = 0 ∨ RatFunc.intDegree f < 0

def ActualDifferentialCartierProper : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    actualRationalProper f → actualRationalProper (actualDifferentialCartier f)

def ActualDifferentialCartierIterateProper : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    actualRationalProper f → ∀ j : Nat,
      actualRationalProper ((actualDifferentialCartier (K := K))^[j] f)

end LogicLineages.OrdinalComparison.Targets
