module
public import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontend
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTest (equalityTest)
open NumberedWindowGuardedGraphTargets (atSlot guard)
open NumberedWindowInternalFreshProbeParsedEmitter
  (addressGood arrowGood rawContext rawResult rawLeast rawDomain rawCodomain)
open NumberedWindowInternalSparseApplicationOutputCore (outputCore)

/-- The two original input addresses are compared by their actual packed
ordered context fields, without decoding to a default context. -/
def sameContext : Program 3 :=
  .composition equalityTest ![atSlot rawContext 0,atSlot rawContext 1]

/-- The function's parsed domain equals the argument's actual result
field. The argument itself need not have an arrow result. -/
def domainAgreement : Program 3 :=
  .composition equalityTest ![atSlot rawDomain 0,atSlot rawResult 1]

/-- The exact physical six-coordinate output call on the original
three-coordinate tape [function, argument, proposed result]. -/
def callOutput (least : Program 3) : Program 3 :=
  .composition (outputCore least)
    ![atSlot rawContext 0,atSlot rawDomain 0,atSlot rawCodomain 0,
      atSlot rawLeast 0,atSlot rawLeast 1,.projection 2]

/-- New physical p₀. Both actual tag3/arity3 checks and the actual source
arrow check precede the comparisons and same least/output call. This core
alone is not claimed to enforce canonical admission. -/
def applicationCore (least : Program 3) : Program 3 :=
  conjunction (atSlot addressGood 0)
    (conjunction (atSlot addressGood 1)
      (conjunction (atSlot arrowGood 0)
        (conjunction sameContext (conjunction domainAgreement (callOutput least)))))

/-- Keep the original installation shape. The same i tests each whole
input exactly once; no output carrier check is inserted. -/
def applicationGuard (i : Program 1) (least : Program 3) : Program 3 :=
  guard i (applicationCore least)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontend
