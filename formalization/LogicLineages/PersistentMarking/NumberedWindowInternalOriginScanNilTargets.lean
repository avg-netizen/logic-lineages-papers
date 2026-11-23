module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanNilTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalRawListRecursion (recGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep zeroBase)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)

def ExactOpenOriginScanNil : Prop :=
  ∀ (side : Bool) (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out scratchLeft rawSide : OrdinaryArithmetic.Term α),
    Nonempty (Derivation B Γ (recGraph zeroBase (rowStep side) out z ![scratchLeft])) →
    Nonempty (Derivation B Γ (loopAccept r out rawSide))

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanNilTargets
