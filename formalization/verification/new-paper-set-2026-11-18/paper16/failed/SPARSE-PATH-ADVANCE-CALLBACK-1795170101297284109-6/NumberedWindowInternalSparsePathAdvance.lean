module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelope
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalLessThan (constantOne)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalSparsePathEnvelope
  (hopGood hopTarget hopSource hopWitness hopRawTarget)

/-- All selected programs use [original packed lexical context, literal
type, encoded current Option, original raw hop code]. -/
def atHop (p : Program 1) : Program 4 :=
  .composition p (fun _ : Fin 1 => .projection 3)

def statePresent : Program 4 := branch (.projection 2) (constantZero 4) (constantOne 4)

def targetCode : Program 4 := .composition .succ (fun _ : Fin 1 => atHop hopTarget)

/-- Inputs to the real raw step check are context, result type, literal
source raw term, witness, literal destination raw term. -/
def rawCall (raw : Program 5) : Program 4 :=
  .composition raw ![.projection 0,.projection 1,atHop hopSource,atHop hopWitness,atHop hopRawTarget]

def leastCall (least : Program 3) (rawTerm : Program 1) : Program 4 :=
  .composition least ![.projection 0,.projection 1,atHop rawTerm]

def fromMatches (least : Program 3) : Program 4 :=
  .composition equalityTest ![leastCall least hopSource,.projection 2]

def toMatches (least : Program 3) : Program 4 :=
  .composition equalityTest ![leastCall least hopRawTarget,targetCode]

/-- Nonempty state and true hop shape are required separately. In particular
an absent least code zero cannot prove an equality with an absent current
state; a real class code zero is represented by one and is not rejected. -/
def advanceGood (raw : Program 5) (least : Program 3) : Program 4 :=
  conjunction statePresent (conjunction (atHop hopGood)
    (conjunction (rawCall raw) (conjunction (fromMatches least) (toMatches least))))

def advance (raw : Program 5) (least : Program 3) : Program 4 :=
  branch (advanceGood raw least) (constantZero 4) targetCode

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvance
