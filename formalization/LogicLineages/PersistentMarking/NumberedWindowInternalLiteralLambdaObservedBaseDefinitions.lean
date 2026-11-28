module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBase
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch conjunction constantZero)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalPush)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)

def lambdaChildCoverage (C : Program 3) (s : Settings) : Program 2 :=
  .composition (conjunction contextPresent (ownSeed C s))
    ![lambdaLexicalPush,constantZero 2,onRaw (field 1)]

def lambdaChildSyntax (Va : Program 1) : Program 2 :=
  callOne Va (onRaw (field 1))

def lambdaChildObservations (C : Program 3) (s : Settings) (Va : Program 1) : Program 2 :=
  conjunction (lambdaChildCoverage C s) (lambdaChildSyntax Va)

/-- Check the actual packed child at the existing lambda branch. The base program
continues to supply the result, including its result arrow. -/
def observedLambdaBase (C : Program 3) (s : Settings) (Va : Program 1)
    (base : Program 2) : Program 2 :=
  branch (onRaw (header 2 2)) base
    (branch (normalize (lambdaChildObservations C s Va)) (constantZero 2) base)

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBase
