module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (branch constantZero conjunction)
open ID1Completion.InternalLessThan (constantOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings admitted vertices)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

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

def syntaxWindow (baseW : Program 3) (V : Program 1) : Program 3 :=
  conjunction baseW (.composition V (fun _ : Fin 1 => .projection 2))

abbrev window (C : Program 3) (s : Settings) (baseW : Program 3) (V : Program 1) :=
  coveredWindow C s (syntaxWindow baseW V)

def ExactSyntaxWindowCalibration : Prop := ∀ (s : Settings) (baseW : Program 3) (V : Program 1),
  ActualPackedWindow s baseW → NumberedWindowInternalSparseTypedRawTargets.ActualRawSyntax V →
    ActualPackedWindow s (syntaxWindow baseW V)

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
