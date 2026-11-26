module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed contextOption)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)

/-- Thin isolated recut of the original matching wrapper program
expressions; the original historical declaration modules stay untouched. -/
def thinOwnSeed (C : Program 3) (s : Settings) : Program 3 :=
  .composition scratchMember ![poolAtSeed C s,.projection 2]

def thinContextPresent : Program 3 := branch contextOption (constantZero 3) (constantOne 3)

def thinCoveredWindow (C : Program 3) (s : Settings) (baseW : Program 3) : Program 3 :=
  conjunction baseW (conjunction thinContextPresent (thinOwnSeed C s))

def thinSyntaxWindow (baseW : Program 3) (V : Program 1) : Program 3 :=
  conjunction baseW (.composition V (fun _ : Fin 1 => .projection 2))

abbrev thinMatchingWindow (C : Program 3) (s : Settings) (baseW : Program 3) (V : Program 1) :=
  thinCoveredWindow C s (thinSyntaxWindow baseW V)

/-- Real physical context check is explicit and no scratch is supplied. -/
def ExactOpenCoverCombinedRestrictedWrapper : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty raw : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    Nonempty (Derivation body Γ (unary P.V (suc z) raw)) →
    Nonempty (Derivation body Γ (windowAt P.W ctx ty raw)) →
    Nonempty (Derivation body Γ (windowAt thinContextPresent ctx ty raw)) →
    Nonempty (Derivation body Γ (windowAt (thinMatchingWindow P.cover s P.W P.V) ctx ty raw))

def ExactOpenCoverThinMatchingWindowReport : Prop :=
  ∀ (C baseW : Program 3) (V : Program 1) (X : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty raw : OTerm α),
    let W := thinMatchingWindow C s baseW V
    Nonempty (Derivation body Γ (windowAt W ctx ty raw)) →
    Nonempty (Derivation body Γ (occursInCover C s raw raw ⊓ hasLeast C X W s ctx ty raw))

def ExactOpenCoverCombinedRestrictedOccurrenceLeast : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (X : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty raw : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    Nonempty (Derivation body Γ (unary P.V (suc z) raw)) →
    Nonempty (Derivation body Γ (windowAt P.W ctx ty raw)) →
    Nonempty (Derivation body Γ (windowAt thinContextPresent ctx ty raw)) →
    Nonempty (Derivation body Γ (occursInCover P.cover s raw raw ⊓ hasLeast P.cover X W s ctx ty raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
