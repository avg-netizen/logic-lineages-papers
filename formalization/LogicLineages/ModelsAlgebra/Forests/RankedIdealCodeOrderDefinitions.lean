module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutableDefinitions
public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder
open RankedIdealRegularCode ForestParseRepresentationCotree
/-- Actual index in the supplied complete list; duplicates do not affect injectivity. -/
def stateOrder (C : Code) : LinearOrder C.machine.State :=
  LinearOrder.lift' (fun q => C.states.idxOf q)
    (fun x _ h => (List.idxOf_inj (C.complete x)).mp h)
def Represents (C : Code) (T : Cotree) : Prop :=
  Reduced T ∧ ∃ t, Nonempty (RankedParse.graph t ≃g graph T) ∧ language C t
def inclusion (C D : Code) : Bool :=
  letI := stateOrder C
  letI := stateOrder D
  CotreePresburgerExecutable.inclusion C.machine D.machine
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder
