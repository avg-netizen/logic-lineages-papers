module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct
open RankedParse ProfileAutomatonEncoding

def rootFlag (o : Operation) (M N : Machine) : Term → Bool
  | .atom => false
  | .node p l r => decide (p = o) && M.accept (machineRun M l) && N.accept (machineRun N r)

def productMachine (o : Operation) (M N : Machine) : Machine where
  State := M.State × N.State × Bool
  stateFintype := inferInstance
  leaf := (M.leaf, N.leaf, false)
  node := fun p x y => (M.node p x.1 y.1, N.node p x.2.1 y.2.1,
    decide (p = o) && M.accept x.1 && N.accept y.2.1)
  accept := fun x => x.2.2

def downwardProduct (o : Operation) (M N : Machine)
    [DecidableEq M.State] [DecidableEq N.State] : Machine :=
  letI : DecidableEq (productMachine o M N).State :=
    inferInstanceAs (DecidableEq (M.State × N.State × Bool))
  RankedIdealMachine.downwardMachine (productMachine o M N)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct
