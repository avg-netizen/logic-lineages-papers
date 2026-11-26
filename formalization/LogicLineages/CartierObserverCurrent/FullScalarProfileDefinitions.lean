module
public import LogicLineages.CartierObserverCurrent.InitialPrincipalPartsProof
public import LogicLineages.CartierObserverCurrent.ProfileOutputDefinitions
public import LogicLineages.CartierObserverCurrent.SourceObserverDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullScalarProfile
open SplittingRoots

/-- Chosen from the already proved UNIQUE genuine initial expansion, not later states. -/
noncomputable def initialCoefficients (d : Nat) (hd : 1 ≤ d) (P : Polynomial (ZMod 2))
    (hP : P.degree < (SourceBudget.denominator (ZMod 2) d).degree) :
    InitialPrincipalParts.Coefficients d (SourceBudget.budget d) :=
  Classical.choose (InitialPrincipalParts.initialSourceCoverage d hd P hP)

/-- Printed beta: coefficient of the INITIAL pole of order1. -/
noncomputable def beta (d : Nat) (hd : 1 ≤ d) (P : Polynomial (ZMod 2))
    (hP : P.degree < (SourceBudget.denominator (ZMod 2) d).degree) (z : Root d) : FieldAt d :=
  initialCoefficients d hd P hP z ⟨0, (SourceBudget.positiveBudgetTransient d hd).1⟩

noncomputable def evolvedBeta (d : Nat) (hd : 1 ≤ d) (P : Polynomial (ZMod 2))
    (hP : P.degree < (SourceBudget.denominator (ZMod 2) d).degree)
    (ell : Nat) (z : Root d) : FieldAt d :=
  ((frobeniusEquiv (FieldAt d) 2).symm)^[ell] (beta d hd P hP z)
end LogicLineages.CartierObserverCurrent.FullScalarProfile
