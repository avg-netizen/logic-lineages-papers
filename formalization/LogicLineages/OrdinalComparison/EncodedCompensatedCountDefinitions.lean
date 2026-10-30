module
public import LogicLineages.OrdinalComparison.EncodedCompensatedStepDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison

def encodedCompensatedState (c n k : Nat) : Nat := (encodedCompensatedStep c)^[k] n

def encodedCompensatedSearch (c n : Nat) : Part Nat :=
  Nat.rfind (fun k => Part.some (encodedFiniteTest (encodedCompensatedState c n k)))

/-- Concrete least-search program. Invalid normal-form codes return zero;
termination on all normal inputs is a separate actual-descent theorem. -/
def encodedCompensatedCountPartial (c n : Nat) : Part Nat :=
  if rawNormalCode n=1 then encodedCompensatedSearch c n else Part.some 0

/-- Semantic total-value wrapper. This declaration alone asserts no effectivity;
uniform Computable₂ and totality of the partial program are separate targets. -/
noncomputable def encodedCompensatedCountValue (c n : Nat) : Nat := by
  classical
  exact (encodedCompensatedCountPartial c n).getOrElse 0

end LogicLineages.OrdinalComparison
