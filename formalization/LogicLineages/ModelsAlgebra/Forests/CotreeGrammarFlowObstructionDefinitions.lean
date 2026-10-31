module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstruction
open CotreeGrammarFlow

def transition (_ _ : Fin 3) : Fin 3 := 1

def terminalWord : List (Finset (Fin 3)) := [{0}, {2}]

/-- A root terminal together with a disconnected circulation 1 → 1 2 and
terminal 2. All balance equations hold, but root 0 cannot branch. -/
def circulation : Counts (Fin 3) :=
  ⟨fun p => if p = (1,2) then 1 else 0,
    fun p => if p = ({0},0) ∨ p = ({2},2) then 1 else 0⟩

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstruction
