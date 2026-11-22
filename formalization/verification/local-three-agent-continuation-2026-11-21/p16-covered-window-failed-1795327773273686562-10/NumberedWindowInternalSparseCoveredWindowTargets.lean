module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero constantOne conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings admitted vertices)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)

def ownSeed (C : Program 3) (s : Settings) : Program 3 :=
  .composition scratchMember ![poolAtSeed C s,.projection 2]

def contextPresent : Program 3 := branch contextOption (constantZero 3) (constantOne 3)

def coveredWindow (C : Program 3) (s : Settings) (baseW : Program 3) : Program 3 :=
  conjunction baseW (conjunction contextPresent (ownSeed C s))

/-- Arbitrary raw lexical and result-type codes, including unused context entries. -/
def WindowSeedsCovered (s : Settings) : Prop := ∀ (ctx : List Nat) (ty q : Nat),
  admitted s ctx ty q = true → q ∈ vertices s q

def ExactCoveredWindowCalibration : Prop := ∀ (C : Program 3) (s : Settings) (baseW : Program 3),
  ActualSelectedCoverOutput C → WindowSeedsCovered s → ActualPackedWindow s baseW →
    ActualPackedWindow s (coveredWindow C s baseW)

/-- Window acceptance entails the original guard, own-cover occurrence, and a
successful least for any physical exchange X using exactly this window program. -/
def ExactCoveredWindowReport : Prop :=
  ∀ (C : Program 3) (X : Program 2) (s : Settings) (baseW : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed : OTerm α),
    let W := coveredWindow C s baseW
    Nonempty (Derivation body Γ ((windowAt W ctx ty seed).imp
      (windowAt baseW ctx ty seed ⊓ (occursInCover C s seed seed ⊓ hasLeast C X W s ctx ty seed))))
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowTargets
