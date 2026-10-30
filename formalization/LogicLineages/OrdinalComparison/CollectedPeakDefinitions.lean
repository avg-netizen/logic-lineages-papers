module
public import LogicLineages.OrdinalComparison.CollectedPositiveDefinitions
public import LogicLineages.OrdinalComparison.PeakOrbitDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def collectedTagEntries : CollectedPositiveTags → List (NONote × CollectedPositiveNF × Nat)
  | .nil => []
  | .cons rho A a rest => (rho,A,a) :: collectedTagEntries rest

def collectedCoefficientSum : CollectedPositiveTags → Nat
  | .nil => 0
  | .cons _ _ a rest => a + collectedCoefficientSum rest

noncomputable def actualCollectedTagInput (rho : NONote) (A : CollectedPositiveNF) (x : Nat) : Ordinal :=
  rho.1.repr + (actualCollectedPositiveEval A x : Ordinal)

noncomputable def actualCollectedTagPeak (rho : NONote) (A : CollectedPositiveNF) (x : Nat) : Nat :=
  actualTerminalValue (actualCollectedTagInput rho A x)

noncomputable def actualCollectedMaximumPeak : CollectedPositiveTags → Nat → Nat
  | .nil, _ => 0
  | .cons rho A _ rest, x => max (actualCollectedTagPeak rho A x) (actualCollectedMaximumPeak rest x)

end LogicLineages.OrdinalComparison
