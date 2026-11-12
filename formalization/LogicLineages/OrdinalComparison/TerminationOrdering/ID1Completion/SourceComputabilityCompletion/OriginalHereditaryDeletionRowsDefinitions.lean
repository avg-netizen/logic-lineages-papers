module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRows
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalClassContextAllPositionObserver
/-- Same original all-position erasure selectors; no rank added to arbitrary Q. -/
def observation (Q : Program 2) : Program 3 :=
  .composition Q ![erasedPacked,erasedParameter]
/-- [index,previous-row,input,parameter], append one observation in cutoff order. -/
def step (Q : Program 2) : Program 4 :=
  .composition InternalApplicationValidityStackAppend.append
    ![.projection 1,.composition InternalListCodec.consCode
      ![.composition (observation Q) ![.projection 0,.projection 2,.projection 3],
        InternalAcceptance.constantZero 4] ]
/-- [count,input,parameter]; bounded primitive recursion, not a hereditary machine. -/
def scan (Q : Program 2) : Program 3 :=
  .recursion (InternalAcceptance.constantZero 2) (step Q)
def rows (Q : Program 2) : Program 2 :=
  .composition (scan Q)
    ![.composition OriginalContextInsertion.length
        (fun _ : Fin 1 => rightOf (.projection 1)),.projection 0,.projection 1]
def values (Q : Program 2) (count input parameter : Nat) : List Nat :=
  (List.range count).map (fun k => evaluate (observation Q)
    (List.Vector.ofFn ![k,input,parameter]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRows
