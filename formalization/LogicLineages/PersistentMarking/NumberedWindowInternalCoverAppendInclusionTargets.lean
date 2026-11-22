module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAppendInclusionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)

/-- Concatenate two original physical layers before and after transport.
The result is an object-calculus inclusion on the actual append lists,
not just an external inclusion on their decoded numerical values. -/
def ExactOpenOriginalAppendInclusion : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (left right leftNext rightNext out outNext : OTerm α),
    Nonempty (Derivation body Γ (appendGraph out left right)) →
    Nonempty (Derivation body Γ (appendGraph outNext leftNext rightNext)) →
    Nonempty (Derivation body Γ (axisInclusion left leftNext)) →
    Nonempty (Derivation body Γ (axisInclusion right rightNext)) →
    Nonempty (Derivation body Γ (axisInclusion out outNext))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAppendInclusionTargets
