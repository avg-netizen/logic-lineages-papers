module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseScalarEdge (edgeGraph edge4)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)

/-- Literal rounds zero and one, on the very same original scratch input.
Neither selected output is definitionally the length-fuelled members pool. -/
structure FirstRoundReports (E : Program 4) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ctx ty vertices src dst before after : OTerm α) : Prop where
  verticesSrc : Nonempty (Derivation body Γ (memberGraph vertices src))
  verticesDst : Nonempty (Derivation body Γ (memberGraph vertices dst))
  edge : Nonempty (Derivation body Γ (acceptEdge E ctx ty src dst))
  zeroRun : Nonempty (Derivation body Γ (roundGraph E before z vertices ctx ty src))
  oneRun : Nonempty (Derivation body Γ (roundGraph E after (suc z) vertices ctx ty src))
  zeroSrc : Nonempty (Derivation body Γ (memberGraph before src))
  oneDst : Nonempty (Derivation body Γ (memberGraph after dst))

def FirstReachK {α : Type} (E : Program 4) (body : Positive (Fin 1))
    (Γ : List (Formula α)) (ctx ty vertices src dst : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (before after : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    FirstRoundReports E body Δ (ctx.relabel j) (ty.relabel j) (vertices.relabel j)
      (src.relabel j) (dst.relabel j) before after →
    Nonempty (Derivation body Δ (goal.relabel j))

def ExactOpenCoverFirstReach : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty vertices a b : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (memberGraph vertices a)) →
    Nonempty (Derivation body Γ (memberGraph vertices b)) →
    Nonempty (Derivation body Γ (acceptEdge E ctx ty a b)) →
    FirstReachK E body Γ ctx ty vertices a b goal →
    Nonempty (Derivation body Γ goal)

def ExactOpenCoverCombinedRestrictedPairedFirstReach : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg m : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let X := guardedExchange P.cover s (thinPairedExchange D)
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) f g)) →
    Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) g f)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m a)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m b)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (vertices before after : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary (coverOption P.cover s) (suc vertices) (a.relabel j))) →
      Nonempty (Derivation body Δ (unary (coverOption P.cover s) (suc vertices) (b.relabel j))) →
      FirstRoundReports (edge4 X W) body Δ (ctx.relabel j) (cod.relabel j) vertices
        (a.relabel j) (b.relabel j) before after →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets
