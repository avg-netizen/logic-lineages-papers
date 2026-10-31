module
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularDefinitions
public import LogicLineages.ModelsAlgebra.Forests.GraphJEPDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput
open ProfileAutomatonEncoding GraphBridge RankedGraphImage

/-- Literal input relation matrix. fromRel removes loops and symmetrizes it,
exactly as the actual comparability graph does; no forest enumeration. -/
def encodeOne (c : FiniteCode.Code) : RawGraph :=
  ⟨c.1, fun i j => decide (FiniteCode.Rel c i.val j.val)⟩

def encode (U : List FiniteCode.Code) : List RawGraph := U.map encodeOne

def pack (G : FiniteSimpleGraph) : FiniteGraph :=
  ⟨G.Carrier, inferInstance, G.graph⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInput
