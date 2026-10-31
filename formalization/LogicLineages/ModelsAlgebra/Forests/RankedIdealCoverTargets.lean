module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCover.Targets
open RankedParse RankedIdealRank RankedIdealComponents RankedIdealCompletion RankedIdealRegularCode RankedGraphImage
 def NonlinearExact : Prop := ∀ C q, nonlinear C q = true ↔ NonlinearAt C.machine q
 def PiecesCorrect : Prop := ∀ C n q, rank C.machine q ≤ n →
   (∀ B ∈ pieces C n q, IsIdeal (language B)) ∧
   ∀ t, (∃ B ∈ pieces C n q, language B t) ↔ Run C.machine t q
 /-- Full actual algorithm correctness, with no cover hypothesis. -/
 def CoverCorrect : Prop := ∀ C,
   (∀ B ∈ cover C, IsIdeal (language B)) ∧
   ∀ t, (∃ B ∈ cover C, language B t) ↔ RankedIdealConstructors.downward (language C) t
 def EmptyExact : Prop := ∀ C, cover C = [] ↔ ∀ t, ¬language C t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCover.Targets
