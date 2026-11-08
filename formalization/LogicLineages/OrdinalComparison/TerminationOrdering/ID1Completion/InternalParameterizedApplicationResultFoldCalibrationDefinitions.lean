module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The EXISTING independent well-founded fold, with the three actual
callbacks sliced at the same arbitrary natural parameter. Its recursion is
on the original term payload, inherited literally from semanticFold. This
definition mentions no transition, state iterator, bounded run, fuel, output
selector or success predicate. No parameter-specialized unary AST is built.
The callback input orders are [value,p] and [domain,codomain,function,argument,p]. -/
def semanticFoldP (guard leaf : Program 2) (combine : Program 5)
    (value parameter : Nat) : Nat :=
  InternalApplicationResultFoldCalibration.semanticFold
    (fun x => evaluate guard (List.Vector.ofFn ![x,parameter]))
    (fun x => evaluate leaf (List.Vector.ofFn ![x,parameter]))
    (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a,parameter])) value

/-- Check the WHOLE final original state of the actual parameterized run,
using the unchanged original goodState AST. It requires status one, empty
work and exactly one result; that result may be zero. The run retains its
original initial state and exact 2*original-payload+1 fuel. Neither a nonzero
fold-output test nor a semantic success oracle is substituted for this AST. -/
def goodRunP (guard leaf : Program 2) (combine : Program 5) : Program 2 :=
  .composition InternalApplicationCertifiedResultFoldClosure.goodState
    (fun _ : Fin 1 => InternalParameterizedApplicationResultStack.runP guard leaf combine)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibration
