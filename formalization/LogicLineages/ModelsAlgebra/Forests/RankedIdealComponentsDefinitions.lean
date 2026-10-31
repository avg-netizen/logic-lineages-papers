module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents
open RankedParse ProfileAutomatonEncoding RankedIdealCompletion RankedIdealFinite

/-- Computable mutual reachability in the productive epsilon graph. -/
def SameComponent (M : Machine) [DecidableEq M.State] (x y : M.State) : Prop :=
  y ∈ close M {x} ∧ x ∈ close M {y}

def stateLanguage (M : Machine) [DecidableEq M.State] (q : M.State) (t : Term) : Prop :=
  Run M t q

/-- An actual binary transition with both productive children and its output
in the same epsilon component as q. No language-directedness premise. -/
def NonlinearAt (M : Machine) [DecidableEq M.State] (q : M.State) : Prop :=
  ∃ o x y, x ∈ productive M ∧ y ∈ productive M ∧
    SameComponent M q x ∧ SameComponent M q y ∧ SameComponent M q (M.node o x y)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents
