module
public import LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncodingDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationGeneralDefinitions

/-! Literal source-family interface for repaired paper03 parse regularity.
The two distinguished forbidden graphs have explicit Boolean matrices; all
remaining input is a finite list of raw finite matrices. No abstract finite
carrier or classical graph encoding is called by this machine construction. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular
open RankedParse RankedGraphImage ProfileAutomatonEncoding

def pathInput : RawGraph := ⟨4, fun x y => decide (x.val + 1 = y.val)⟩
def cycleInput : RawGraph := ⟨4, fun x y => decide ((x.val + 1) % 4 = y.val)⟩
def rawFinite (A : RawGraph) : FiniteGraph := ⟨Fin A.1, inferInstance, rawGraph A⟩
def sourceMachine (F : List RawGraph) : Machine := machine (pathInput :: cycleInput :: F)

def sourceFamily (B : List FiniteGraph) : List FiniteGraph :=
  ⟨Fin 4, inferInstance, GraphBridge.fourPath⟩ ::
  ⟨Fin 4, inferInstance, GraphBridge.fourCycle⟩ :: B

end LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular
