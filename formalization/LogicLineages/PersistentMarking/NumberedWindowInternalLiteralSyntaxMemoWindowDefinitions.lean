module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindow
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch constantZero)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxUpdate)

def syntaxAtKey (V : Program 1) : Program 4 := unaryAfter V currentKey

/-- Keep the original strict auxiliary node's recursive table. In every
specific row, including each independently called child row, record the
same original raw syntax gate at the actual raw key. -/
def update (base : Program 2) (T V : Program 1) : Program 4 :=
  branch (normalize (syntaxAtKey V)) (constantZero 4) (strictAuxUpdate base T)

def intrinsic (base : Program 2) (T V : Program 1) : Program 2 := selectedIntrinsic (update base T V)

def window (base : Program 2) (T V : Program 1) : Program 3 :=
  intrinsicQuery (intrinsic base T V)

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindow
