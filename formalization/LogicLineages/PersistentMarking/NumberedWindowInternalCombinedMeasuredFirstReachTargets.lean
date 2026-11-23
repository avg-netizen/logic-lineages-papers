module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachTargets
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
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets (CrossCoverReports)
open NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets (FirstRoundReports)
open NumberedWindowInternalCombinedMeasuredRouteTargets (InstalledRoute install)

/-- Expose one genuine ordered scratch code with both original endpoint reports.
There is no external cover, endpoint-window or measure premise. -/
def InstalledCrossCoverK {α : Type} (K : InstalledRoute) (body : Positive (Fin 1))
    (Γ : List (Formula α)) (ctx ty a b : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (vertices : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    CrossCoverReports K.cover K.settings body Δ (a.relabel j) (b.relabel j) vertices →
    Nonempty (Derivation body Δ (acceptEdge K.edge (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j))) →
    Nonempty (Derivation body Δ (goal.relabel j))

def ExactInstalledMeasuredCrossCover : Prop :=
  ∀ (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty a b : OTerm α) (goal : Formula α),
    let K := install s V TV M M0 B T base
    Nonempty (Derivation body Γ (acceptEdge K.edge ctx ty a b)) →
    InstalledCrossCoverK K body Γ ctx ty a b goal →
    Nonempty (Derivation body Γ goal)

/-- The caller sees rounds at literal zero and one, on the one actual original
scratch tape and over the very same installed measured edge program. -/
def InstalledFirstReachK {α : Type} (K : InstalledRoute) (body : Positive (Fin 1))
    (Γ : List (Formula α)) (ctx ty a b : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (vertices before after : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    Nonempty (Derivation body Δ (unary (coverOption K.cover K.settings) (suc vertices) (a.relabel j))) →
    Nonempty (Derivation body Δ (unary (coverOption K.cover K.settings) (suc vertices) (b.relabel j))) →
    FirstRoundReports K.edge body Δ (ctx.relabel j) (ty.relabel j) vertices
      (a.relabel j) (b.relabel j) before after →
    Nonempty (Derivation body Δ (goal.relabel j))

def ExactInstalledMeasuredFirstReach : Prop :=
  ∀ (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty a b : OTerm α) (goal : Formula α),
    let K := install s V TV M M0 B T base
    Nonempty (Derivation body Γ (acceptEdge K.edge ctx ty a b)) →
    InstalledFirstReachK K body Γ ctx ty a b goal →
    Nonempty (Derivation body Γ goal)

/-- The measured replacement for the existing paired first-reach caller.
The two independent type guards and argument window are retained; the single
function edge already carries the actual selected comparison. -/
def ExactInstalledMeasuredApplicationFirstReach : Prop :=
  ∀ (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg : OTerm α) (goal : Formula α),
    let K := install s V TV M M0 B T base
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt K.window ctx dom arg)) →
    Nonempty (Derivation body Γ (acceptEdge K.edge ctx (rawCons dom cod) f g)) →
    InstalledFirstReachK K body Γ ctx cod (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg) goal →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachTargets
