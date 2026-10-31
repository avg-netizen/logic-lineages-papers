module
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhDefinitions
public import Mathlib.Data.Finset.Image
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition
open FirstOrder Language RankedParse ProfileAutomatonEncoding CotreePresburger CotreeMachineParikh

/-- Choice-free source-variable compiler from an explicitly numbered finite machine.
The numerical table formula is relabeled back to the original child-state subsets. -/
def compileNumbered (M : Machine) {k : Nat} (e : M.State ≃ Fin k)
    (o : Operation) (q : M.State) : PFormula (Finset M.State) :=
  Formula.relabel e.finsetCongr.symm (tableFormula (numberMachine M e) o (e q))

end LogicLineages.ModelsAlgebra.Forests.ForestParikhTransition
