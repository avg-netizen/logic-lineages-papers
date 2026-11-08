module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizer
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs are [candidate, original value, parameter]. The ORIGINAL left
selector is applied to the candidate and original VALUE, not to the carried
state or the parameter. These are the source-value type tags. -/
def sameLeft : Program 3 :=
  .composition InternalEqualityTest.equalityTest
    (Fin.cons
      (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (0 : Fin 3)))
      (Fin.cons
        (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (1 : Fin 3)))
        Fin.elim0))

/-- Strict descent compares only [candidate, original value]. The runtime
parameter and the numeric code of the carried pair are not measured. -/
def candidateLess : Program 3 :=
  .composition InternalLessThan.ltTest
    (Fin.cons (.projection (0 : Fin 3))
      (Fin.cons (.projection (1 : Fin 3)) Fin.elim0))

/-- The arbitrary binary validity AST receives [candidate, parameter].
The guard below accepts its output only when it is EXACTLY one. -/
def candidateValid (valid : Program 2) : Program 3 :=
  .composition valid
    (Fin.cons (.projection (0 : Fin 3))
      (Fin.cons (.projection (2 : Fin 3)) Fin.elim0))

/-- All three tests must accept. No calibration, Boolean-range,
preservation or termination assumption is imposed on either binary leaf. -/
def guard (valid : Program 2) : Program 3 :=
  InternalAcceptance.conjunction candidateLess
    (InternalAcceptance.conjunction (candidateValid valid) sameLeft)

/-- The original conditional receives control, zero branch, nonzero branch.
Rejection returns the original VALUE; acceptance returns the candidate. -/
def choose (valid : Program 2) : Program 3 :=
  InternalAcceptance.branch (guard valid) (.projection (1 : Fin 3))
    (.projection (0 : Fin 3))

/-- Inputs are [value, parameter]. Compute R(value,parameter), then choose
on [candidate,value,parameter]. Both leaves are actual binary ASTs fixed
before any symbolic parameter, variable type, context or term is supplied. -/
def transition (representative valid : Program 2) : Program 2 :=
  .composition (choose valid)
    (Fin.cons representative
      (Fin.cons (.projection (0 : Fin 2))
        (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))

/-- B(value,parameter) is the ACTUAL parameter-carrying repeat AST at
[value+1,value,parameter]. Fuel depends on the VALUE, never pair(parameter,
value). The original numeric recursion carries the identical parameter. -/
def normalizer (representative valid : Program 2) : Program 2 :=
  .composition
    (InternalParameterizedNumericIteration.repeatP (transition representative valid))
    (Fin.cons
      (.composition .succ (fun _ : Fin 1 => .projection (0 : Fin 2)))
      (Fin.cons (.projection (0 : Fin 2))
        (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))

def binaryGraph {α : Type} (p : Program 2)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph p out (Fin.cons input (Fin.cons parameter Fin.elim0))

def transitionGraph {α : Type} (representative valid : Program 2)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  binaryGraph (transition representative valid) out input parameter

def normalizerGraph {α : Type} (representative valid : Program 2)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  binaryGraph (normalizer representative valid) out input parameter

def validGraph {α : Type} (valid : Program 2)
    (input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  binaryGraph valid (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    input parameter

/-- The ORIGINAL left selector of the source value. This is independent
of the left coordinate used to carry the runtime parameter during iteration. -/
def leftGraph {α : Type} (typ input : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph InternalUnpair.left typ (Fin.cons input Fin.elim0)

/-- Object-language weak order on VALUES: lower < successor upper. -/
def atMost {α : Type} (lower upper : OrdinaryArithmetic.Term α) : Formula α :=
  InternalLessThan.strictLess lower (OrdinaryArithmetic.succTerm upper)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizer
