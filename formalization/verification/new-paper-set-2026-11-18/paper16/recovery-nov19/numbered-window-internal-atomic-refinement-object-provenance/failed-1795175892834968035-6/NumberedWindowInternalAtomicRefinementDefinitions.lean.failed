module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinement
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt literal chooseBranch bothOne compareNumbers)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary nodeGood field)

/-- The same physical first field of the original raw least term. -/
def storedType : Program 1 := applyUnary (field 0) rawLeast

def storedTypeFits : Program 1 :=
  .composition compareNumbers (Fin.cons rawResult (Fin.cons storedType Fin.elim0))

/-- Structure, not lexical admission: outer tag3 exact3, then the raw
least term's literal tag/arity and the same stored/result type. -/
def atomSource (tag fields : Nat) : Program 1 :=
  bothOne addressGood
    (bothOne (applyUnary (nodeGood (literal 1 tag) fields) rawLeast) storedTypeFits)

def freeSource : Program 1 := atomSource 0 2
def bottomSource : Program 1 := atomSource 3 1

/-- The literal sparse constructor uses the same raw packed context and
result field. It never parses or re-encodes the context. -/
def bottomEmitter : Program 2 :=
  let ctx : Program 2 := .projection 0
  let t : Program 2 := .projection 1
  let tag := literal 2 3
  let z := zeroAt 2
  let payload := consOf tag (consOf t z)
  consOf tag (consOf ctx (consOf t (consOf payload z)))

def bottomOf : Program 1 :=
  .composition bottomEmitter (Fin.cons rawContext (Fin.cons rawResult Fin.elim0))

def atSource (p : Program 1) : Program 3 :=
  .composition p (fun _ : Fin 1 => .projection (0 : Fin 3))

def atTarget (p : Program 1) : Program 3 :=
  .composition p (fun _ : Fin 1 => .projection (2 : Fin 3))

/-- Exact target comparison in the actual [source,witness,target] tape.
The original witness is not read, replaced, or reconstructed here. -/
def bottomTarget : Program 3 :=
  .composition compareNumbers (Fin.cons (.projection (2 : Fin 3))
    (Fin.cons (atSource bottomOf) Fin.elim0))

/-- This is one actual replacement AST for the positive checker only.
The old positive program runs on all three unchanged inputs.
Nonatomic inputs retain its value; literal bottom rejects; literal
free success also checks the exact bottom and actual scalar output. -/
def refined (i : Program 1) (r : Program 3) : Program 3 :=
  chooseBranch (atSource freeSource)
    (chooseBranch (atSource bottomSource) r (zeroAt 3))
    (bothOne r (bothOne bottomTarget (atTarget i)))

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinement
