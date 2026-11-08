module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizer
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs are [candidate, original]. The ORIGINAL left selector is applied
to each input; equality is tested by the existing exact equality AST. -/
def sameLeft : Program 2 :=
  .composition InternalEqualityTest.equalityTest
    (Fin.cons
      (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (0 : Fin 2)))
      (Fin.cons
        (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (1 : Fin 2)))
        Fin.elim0))

/-- Candidate validity is the actual arbitrary unary Program leaf.
The conjunction below tests its output for EXACT equality to one. -/
def candidateValid (valid : Program 1) : Program 2 :=
  .composition valid (fun _ : Fin 1 => .projection (0 : Fin 2))

/-- Inputs are [candidate, original]. All three tests must accept:
candidate < original, valid(candidate) = 1, and equal original left tags.
No totality, Boolean-range, calibration or preservation premise is supplied. -/
def guard (valid : Program 1) : Program 2 :=
  InternalAcceptance.conjunction InternalLessThan.ltTest
    (InternalAcceptance.conjunction (candidateValid valid) sameLeft)

/-- Rejection returns the original input; acceptance returns the candidate.
The conditional's argument order is control, zero branch, nonzero branch. -/
def choose (valid : Program 1) : Program 2 :=
  InternalAcceptance.branch (guard valid) (.projection (1 : Fin 2))
    (.projection (0 : Fin 2))

/-- T(x): compute r = representative(x), then choose on [r,x].
The representative and validity leaves are completely arbitrary original ASTs.
An accepted move strictly decreases the number; every rejected move fixes it. -/
def transition (representative valid : Program 1) : Program 1 :=
  .composition (choose valid)
    (Fin.cons representative (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))

/-- B(x) is the ORIGINAL numeric repeat AST on [x+1,x]. There is no
external fuel, bounded-search oracle, new recursion rule or selected witness. -/
def normalizer (representative valid : Program 1) : Program 1 :=
  .composition (InternalNumericIteration.repeatProgram (transition representative valid))
    (Fin.cons .succ (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))

def unaryGraph {α : Type} (p : Program 1)
    (out input : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph p out (Fin.cons input Fin.elim0)

def transitionGraph {α : Type} (representative valid : Program 1)
    (out input : OrdinaryArithmetic.Term α) : Formula α :=
  unaryGraph (transition representative valid) out input

def normalizerGraph {α : Type} (representative valid : Program 1)
    (out input : OrdinaryArithmetic.Term α) : Formula α :=
  unaryGraph (normalizer representative valid) out input

def validGraph {α : Type} (valid : Program 1)
    (input : OrdinaryArithmetic.Term α) : Formula α :=
  unaryGraph valid (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) input

def leftGraph {α : Type} (typ input : OrdinaryArithmetic.Term α) : Formula α :=
  unaryGraph InternalUnpair.left typ input

/-- Object-language weak order: lower < successor upper. -/
def atMost {α : Type} (lower upper : OrdinaryArithmetic.Term α) : Formula α :=
  InternalLessThan.strictLess lower (OrdinaryArithmetic.succTerm upper)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizer
