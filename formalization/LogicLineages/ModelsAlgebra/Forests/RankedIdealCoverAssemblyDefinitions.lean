module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCodeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssembly
open RankedIdealRegularCode RankedIdealSpineCode

def linearPieces (C : Code) (q : C.machine.State)
    (rec : C.machine.State → List Code) : List Code :=
  (seeds C q rec).map (fun B => linearList B (frames C q))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssembly
