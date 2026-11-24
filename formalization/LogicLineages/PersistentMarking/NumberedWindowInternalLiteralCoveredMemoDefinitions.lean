module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemo
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch conjunction constantZero)
open NumberedWindowScalarAlgorithm (Settings admitted vertices)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan (constantOne)
open NumberedWindowInternalLiteralSyntaxMemoWindow (update)

/-- These are the original two physical finite-cover checks, without
the unrelated higher-order exchange transport dependencies. -/
def contextPresent : Program 3 := branch contextOption (constantZero 3) (constantOne 3)
def ownSeed (C : Program 3) (s : Settings) : Program 3 :=
  .composition scratchMember ![poolAtSeed C s,.projection 2]

def WindowSeedsCovered (s : Settings) : Prop :=
  ∀ (ctx : List Nat) (ty q : Nat), admitted s ctx ty q = true → q ∈ vertices s q

/-- Both physical obligations for a successful least. The dummy type
is not consulted by either calculation. The context and the current
successor key are the exact original row's. -/
def coverageAtKey (C : Program 3) (s : Settings) : Program 4 :=
  .composition (conjunction contextPresent (ownSeed C s)) ![.projection 2,constantZero 4,currentKey]

/-- Check the original finite cover at every successful row of the
same memo, including each child independently; no old table is reused. -/
def coveredUpdate (C : Program 3) (s : Settings) (base : Program 2)
    (T V : Program 1) : Program 4 :=
  branch (normalize (coverageAtKey C s)) (constantZero 4) (update base T V)

def coveredIntrinsic (C : Program 3) (s : Settings) (base : Program 2)
    (T V : Program 1) : Program 2 := selectedIntrinsic (coveredUpdate C s base T V)

def coveredMemoWindow (C : Program 3) (s : Settings) (base : Program 2)
    (T V : Program 1) : Program 3 := intrinsicQuery (coveredIntrinsic C s base T V)

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemo
