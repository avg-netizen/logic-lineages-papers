module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow)
open NumberedWindowInternalCoverOwnEarlierTargets (ownAt)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)

def PointOwnStep (P : Programs) (s : Settings) (body : Positive (Fin 1)) : Prop :=
  ∀ (β : Type) (Δ : List (Formula β)) (raw p vertices ctx result : OTerm β),
    ParentRow P s body Δ raw p vertices ctx result →
    Nonempty (Derivation body Δ (memberGraph vertices raw))

/-- The original object family at each raw key, with its actual
validity condition and typed context/result/scratch antecedents. -/
def ExactOpenCoverCombinedRestrictedOwnFamily : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    Nonempty (Derivation body Γ (ownAt P.V P.W P.cover s raw))

/-- No separately supplied measure witness or earlier-own induction
hypothesis. The actual selected validity, W and held scratch remain. -/
def ExactOpenCoverCombinedRestrictedInductionOwn : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw vertices ctx result : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    Nonempty (Derivation body Γ (unary P.V (suc z) raw)) →
    Nonempty (Derivation body Γ (windowAt P.W ctx result raw)) →
    Nonempty (Derivation body Γ (unary (scratchVertices P.cover s) vertices raw)) →
    Nonempty (Derivation body Γ (memberGraph vertices raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionTargets
