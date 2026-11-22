module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)

/-- Actual all-seven bounded step on one selected restricted program.
The original genuine earlier-own formula is still held in ParentRow. -/
def ExactOpenCoverCombinedRestrictedBoundedStep : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw p vertices ctx result : OTerm α),
    ParentRow (combinedPrograms s V TV M M0 B T) s body Γ raw p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepTargets
