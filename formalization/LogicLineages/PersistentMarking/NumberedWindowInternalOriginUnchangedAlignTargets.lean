module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginBothRemovedNonemptyTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginUnchangedAlignTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalOriginBothRemovedNonemptyTargets (D)

def ExactOpenOriginUnchangedJoinedEq : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (kept removed projected sourceJoin targetJoin : OTerm α),
    D B Γ (eqn removed z) → D B Γ (eqn projected z) →
    D B Γ (appendGraph sourceJoin kept removed) →
    D B Γ (appendGraph targetJoin kept projected) →
    D B Γ (eqn sourceJoin targetJoin)

def ExactOpenOriginUnchangedAlign : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (source kept removed projected sourceJoin targetJoin : OTerm α),
    D B Γ (eqn removed z) → D B Γ (eqn projected z) →
    D B Γ (appendGraph sourceJoin kept removed) →
    D B Γ (appendGraph targetJoin kept projected) →
    D B Γ (observer permutation source sourceJoin) →
    D B Γ (observer permutation source targetJoin)

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginUnchangedAlignTargets
