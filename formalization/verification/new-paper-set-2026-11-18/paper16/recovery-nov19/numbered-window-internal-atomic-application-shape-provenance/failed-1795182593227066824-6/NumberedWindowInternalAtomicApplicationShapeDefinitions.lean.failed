module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShape
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt literal compareNumbers chooseBranch bothOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawDomain rawCodomain rawLeast arrowGood)
open NumberedWindowInternalSparsePathEnvelope (applyUnary field)
open NumberedWindowInternalAtomicRefinement (atSource atTarget freeSource bottomSource)

/-- Literal sparse tag3/[context,result,least] constructor on raw coordinates. -/
def addressEmitter : Program 3 :=
  let c : Program 3 := .projection 0
  let t : Program 3 := .projection 1
  let k : Program 3 := .projection 2
  let z := zeroAt 3
  consOf (literal 3 3) (consOf c (consOf t (consOf k z)))

/-- Raw context, domain, result, exact raw function, raw argument in
this order. Construct the literal original tag6 node inside tag3. -/
def auxAddressEmitter : Program 5 :=
  let c : Program 5 := .projection 0
  let d : Program 5 := .projection 1
  let e : Program 5 := .projection 2
  let k : Program 5 := .projection 3
  let a : Program 5 := .projection 4
  let z := zeroAt 5
  let k' := consOf (literal 5 6) (consOf d (consOf e (consOf k (consOf a z))))
  consOf (literal 5 3) (consOf c (consOf e (consOf k' z)))

/-- The inspected tape is [function,argument,result], not a certificate
tape. The reported output argument is the actual last raw aux field. -/
def fromArgument (p : Program 1) : Program 3 :=
  .composition p (fun _ : Fin 1 => .projection (1 : Fin 3))

def auxArgument : Program 1 := applyUnary (field 3) rawLeast

def rebuildArgument : Program 3 :=
  .composition addressEmitter
    (Fin.cons (atSource rawContext) (Fin.cons (atSource rawDomain)
      (Fin.cons (fromArgument rawLeast) Fin.elim0)))

def rebuildResult : Program 3 :=
  .composition auxAddressEmitter
    (Fin.cons (atSource rawContext) (Fin.cons (atSource rawDomain) (Fin.cons (atSource rawCodomain)
      (Fin.cons (atSource rawLeast) (Fin.cons (atTarget auxArgument) Fin.elim0)))))

def sameArgument : Program 3 :=
  .composition compareNumbers (Fin.cons (.projection (1 : Fin 3)) (Fin.cons rebuildArgument Fin.elim0))

def sameResult : Program 3 :=
  .composition compareNumbers (Fin.cons (.projection (2 : Fin 3)) (Fin.cons rebuildResult Fin.elim0))

def atomicChecks : Program 3 :=
  bothOne (atSource arrowGood) (bothOne sameArgument sameResult)

def atomBranch (p : Program 3) : Program 3 := bothOne p atomicChecks

/-- Nonatomic inputs retain the unchanged old Program on the same three
coordinates. Only the literal atom branch checks both re-emissions,
with no scalar output premise or additional lexical admission claim. -/
def refinedApplication (p : Program 3) : Program 3 :=
  chooseBranch (atSource freeSource)
    (chooseBranch (atSource bottomSource) p (atomBranch p)) (atomBranch p)

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShape
