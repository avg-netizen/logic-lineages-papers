module

public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions

@[expose] public section

/-! Literal source Pi_2 clause: every p-annihilated element has a p^j root.
Here j is source k-1. The implication is built from the original finite QF
negation/conjunction syntax; there are no extra filtration predicates. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth

def socleRootMatrix (p j n : ℕ) : QF ((n + 1) + 1) :=
  let x : GroupTerm ((n + 1) + 1) := .var (Fin.castAdd 1 (Fin.natAdd n (0 : Fin 1)))
  let y : GroupTerm ((n + 1) + 1) := .var (Fin.natAdd (n + 1) (0 : Fin 1))
  .neg (.and (.equal (multipleTerm p x) .zero)
    (.neg (.equal (multipleTerm (p ^ j) y) x)))

def socleRootWitnessFormula (p j n : ℕ) : Formula (n + 1) :=
  .disjEx {0} (fun _ => 1) (fun _ => .qf (socleRootMatrix p j n))

def socleRootFormula (p j n : ℕ) : Formula n :=
  .conjAll {0} (fun _ => 1) (fun _ => socleRootWitnessFormula p j n)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
