module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositive
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparseAddressPositive (atAddress sideGood sameField addressPositive)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)

def wrapFoldAt (P : Program 5) : Program 3 :=
  .composition P
    ![atAddress rawContext 0, atAddress rawResult 0, atAddress rawLeast 0,
      .projection 1, atAddress rawLeast 2]

def addressAt (ctxValid tyValid : Program 1) (P : Program 5) : Program 3 :=
  conjunction (sideGood ctxValid tyValid 0)
    (conjunction (sideGood ctxValid tyValid 2)
      (conjunction (sameField rawContext) (conjunction (sameField rawResult) (wrapFoldAt P))))

def zeroAddress (ctxValid tyValid g : Program 1) (raw : Program 5) (L : Program 3) : Program 3 :=
  addressAt ctxValid tyValid (zeroPositive g raw L)

theorem exact_OriginalAddressAt (cv tv : Program 1) (raw : Program 5) (L : Program 3) :
    addressAt cv tv (positive raw L) = addressPositive cv tv raw L := rfl

#print axioms exact_OriginalAddressAt

end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositive
