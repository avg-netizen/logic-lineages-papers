module
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhDefinitions
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhProfile
open RankedParse FiniteProfile ProfileAutomatonEncoding CotreePresburger CotreeMachineParikh

/-- Finite Boolean mask/matrix serialization, retaining every code bit. -/
def codeKey {N : Nat} (C : Code N) : List Bool ×ₗ List (List Bool) :=
  toLex (List.ofFn C.1, List.ofFn (fun i => List.ofFn (C.2 i)))

theorem codeKeyInjective (N : Nat) : Function.Injective (codeKey (N := N)) := by
  intro C D h
  apply Prod.ext
  · exact List.ofFn_injective (congrArg (fun x => (ofLex x).1) h)
  · have hr := List.ofFn_injective (congrArg (fun x => (ofLex x).2) h)
    funext i
    exact List.ofFn_injective (congrFun hr i)

/-- Computable list-lex order, not the choice-based order on arbitrary functions. -/
def codeOrder (N : Nat) : LinearOrder (Code N) :=
  LinearOrder.lift' codeKey (codeKeyInjective N)

def stateOrder (N : Nat) : LinearOrder (State N) := by
  letI := codeOrder N
  exact LinearOrder.lift' (fun S : State N => toColex S) (fun _ _ h => h)

/-- A literal raw forbidden-graph family compiles directly to actual Presburger
transition syntax through its concrete profile machine and computable code order. -/
def profileFormula (F : List RawGraph) (o : Operation) (q : (machine F).State) :
    PFormula (Finset (machine F).State) := by
  letI : LinearOrder (machine F).State := stateOrder (familyBound F)
  exact transitionFormula (machine F) o q

end LogicLineages.ModelsAlgebra.Forests.ForestParikhProfile
