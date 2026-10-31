module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCountsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh
open RankedParse ProfileAutomatonEncoding CotreePresburger

/-- Actual Presburger syntax computed from the given finite ordered transition table. -/
def transitionFormula (M : Machine) [LinearOrder M.State] (o : Operation) (q : M.State) :
    PFormula (Finset M.State) := formula (M.node o) q

/-- Literal finite input encoding. Every state is an actual numerical index;
constructing formulas from this table requires no choice of an enumeration. -/
structure TableMachine where
  size : Nat
  leaf : Fin size
  node : Operation → Fin size → Fin size → Fin size
  accept : Fin size → Bool

def TableMachine.toMachine (T : TableMachine) : Machine where
  State := Fin T.size
  stateFintype := inferInstance
  leaf := T.leaf
  node := T.node
  accept := T.accept

def tableFormula (T : TableMachine) (o : Operation) (q : Fin T.size) :
    PFormula (Finset (Fin T.size)) := formula (T.node o) q

/-- Executable reindexing when a numbering is supplied as explicit input data.
No noncomputable selection of an equivalence is part of the compiler. -/
def numberMachine (M : Machine) {n : Nat} (e : M.State ≃ Fin n) : TableMachine where
  size := n
  leaf := e M.leaf
  node o x y := e (M.node o (e.symm x) (e.symm y))
  accept x := M.accept (e.symm x)

end LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikh
