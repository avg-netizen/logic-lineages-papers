module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssemblyDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssembly.Targets
open RankedIdealRegularCode RankedIdealSpineCode RankedIdealComponents RankedIdealCompletion RankedGraphImage

def PiecesIdeal : Prop := ∀ C q rec, LowerCorrect C q rec →
  ∀ B ∈ linearPieces C q rec, IsIdeal (language B)

/-- Conditional assembly supplier only. The recursive algorithm must discharge
LowerCorrect for every strict predecessor; it is not an ideal-cover oracle. -/
def PiecesExact : Prop := ∀ C q rec, LowerCorrect C q rec → ¬NonlinearAt C.machine q →
  ∀ t, (∃ B ∈ linearPieces C q rec, language B t) ↔ Run C.machine t q
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssembly.Targets
