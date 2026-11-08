module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStack
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal weakening of an original unary AST. Inputs are [value,parameter];
the second input is ignored, not encoded in the original state or worklist. -/
def liftP (P : Program 1) : Program 2 :=
  .composition P (fun _ : Fin 1 => .projection (0 : Fin 2))

/-- Append the unchanged parameter AFTER all original coordinates. This is
finite argument wiring, not an evaluator or a source-code interpreter. -/
def appendParameter {n : Nat} {α : Type} (xs : Fin n → α) (parameter : α) : Fin (n+1) → α :=
  Fin.lastCases parameter xs

/-- Apply an actual (n+1)-ary AST to n original unary selectors of input 0
and then the unchanged parameter from input 1. The AST is chosen before
any symbolic arithmetic terms, body or logical context are supplied. -/
def wireP {n : Nat} (P : Program (n+1)) (selectors : Fin n → Program 1) : Program 2 :=
  .composition P (appendParameter (fun i => liftP (selectors i)) (.projection (1 : Fin 2)))

/-- Inputs [originalPackedValue,parameter]. The first conjunct is the
ORIGINAL tag-two test. Only an exact-one G(value,parameter) opens the root. -/
def openGuardP (guard : Program 2) : Program 2 :=
  InternalAcceptance.conjunction
    (liftP (InternalApplicationStepPeel.same
      (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1))) guard

/-- Inputs [originalState,parameter]. Return L(currentValue,parameter)
through the ORIGINAL returnState with the unchanged work and result suffixes. -/
def leafReturnedP (leaf : Program 2) : Program 2 :=
  .composition InternalApplicationResultStack.returnState
    ![wireP leaf ![InternalApplicationResultStack.currentValue],
      liftP InternalApplicationResultStack.rest, liftP InternalApplicationResultStack.results]

/-- The exact C input order is [domain,codomain,functionOutput,argumentOutput,
parameter], although the ORIGINAL result stack stores argument before function. -/
def combinedP (combine : Program 5) : Program 2 :=
  wireP combine
    ![leftOf InternalApplicationResultStack.currentValue,
      rightOf InternalApplicationResultStack.currentValue,
      InternalApplicationResultStack.headOf
        (InternalApplicationResultStack.tailOf InternalApplicationResultStack.results),
      InternalApplicationResultStack.headOf InternalApplicationResultStack.results]

def finishReturnedP (combine : Program 5) : Program 2 :=
  .composition InternalApplicationResultStack.returnState
    ![combinedP combine, liftP InternalApplicationResultStack.rest,
      liftP (InternalApplicationResultStack.tailOf
        (InternalApplicationResultStack.tailOf InternalApplicationResultStack.results))]

/-- The ORIGINAL branch tree on [state,parameter], with every state selector
lifted through input 0. Malformed frames, non-one status and short result
stacks still fail at zero. Expansion is the original unary expansion AST.
Only the three callback applications receive the appended parameter. -/
def transitionP (guard leaf : Program 2) (combine : Program 5) : Program 2 :=
  InternalAcceptance.branch
    (liftP (InternalApplicationValidityStack.exactOne InternalApplicationResultStack.status))
    (InternalAcceptance.constantZero 2)
    (InternalAcceptance.branch (liftP InternalApplicationResultStack.work) (.projection 0)
      (InternalAcceptance.branch
        (liftP (InternalApplicationStepPeel.same InternalApplicationResultStack.frameTag
          (InternalAcceptance.constantZero 1)))
        (InternalAcceptance.branch
          (liftP (InternalApplicationValidityStack.exactOne InternalApplicationResultStack.frameTag))
          (InternalAcceptance.constantZero 2)
          (InternalAcceptance.branch (liftP InternalApplicationResultStack.results)
            (InternalAcceptance.constantZero 2)
            (InternalAcceptance.branch
              (liftP (InternalApplicationResultStack.tailOf InternalApplicationResultStack.results))
              (InternalAcceptance.constantZero 2) (finishReturnedP combine))))
        (InternalAcceptance.branch
          (wireP (openGuardP guard) ![InternalApplicationResultStack.currentValue])
          (leafReturnedP leaf) (liftP InternalApplicationResultStack.expanded))))

/-- Inputs [count,originalState,parameter]. The existing parameterized numeric
iterator carries p outside the original result-stack state. No work frame,
result entry, source codec or transition fuel is changed. -/
def iterateP (guard leaf : Program 2) (combine : Program 5) : Program 3 :=
  InternalParameterizedNumericIteration.repeatP (transitionP guard leaf combine)

/-- Inputs [originalPackedValue,parameter]. Fuel and initial state are exactly
the original unary programs. The parameter contributes NOTHING to fuel. -/
def runP (guard leaf : Program 2) (combine : Program 5) : Program 2 :=
  .composition (iterateP guard leaf combine)
    ![liftP InternalApplicationResultStack.fuel,
      liftP InternalApplicationResultStack.initial, .projection 1]

/-- Expose the actual bounded AST, using the unchanged original output
selector. No full-run shape, recursive fold, append/framing, representative
identification or uniform correctness claim is part of this local packet. -/
def foldP (guard leaf : Program 2) (combine : Program 5) : Program 2 :=
  .composition InternalApplicationResultStack.output (fun _ : Fin 1 => runP guard leaf combine)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStack
