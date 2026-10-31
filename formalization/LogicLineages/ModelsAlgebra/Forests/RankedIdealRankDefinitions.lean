module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealComponentsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRank
open ProfileAutomatonEncoding RankedIdealFinite
/-- Explicit finite epsilon predecessors, including the state itself. -/
def predecessors (M : Machine) [DecidableEq M.State] (q : M.State) : Finset M.State :=
  Finset.univ.filter (fun p => q ∈ close M {p})
def rank (M : Machine) [DecidableEq M.State] (q : M.State) : Nat :=
  (predecessors M q).card
def Lower (M : Machine) [DecidableEq M.State] (p q : M.State) : Prop :=
  q ∈ close M {p} ∧ p ∉ close M {q}
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRank
