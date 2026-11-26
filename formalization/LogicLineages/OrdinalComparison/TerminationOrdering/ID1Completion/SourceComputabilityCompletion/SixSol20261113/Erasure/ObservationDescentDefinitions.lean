module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
/-- Proof-side selectors only: false selects original left, true original right.
Paths are applied from the input inward. No evaluator or source AST is changed. -/
def select : List Bool → Program 1
 | [] => .projection 0
 | b :: ps => .composition (select ps) (fun _ : Fin 1 => if b then InternalUnpair.right else InternalUnpair.left)
inductive DirectSlot where
 | lambdaBody | function | argument
inductive ListSlot where
 | ordinaryBase | numberedBase | numberedExtras
/-- Literal typed-child paths inside the ORIGINAL recursive-root payload. -/
def directPath : DirectSlot → List Bool
 | .lambdaBody => [true,true]
 | .function => [true,true,false]
 | .argument => [true,true,true]
def directTag : DirectSlot → Nat
 | .lambdaBody => 1
 | .function => 2
 | .argument => 2
/-- Literal list paths inside the ORIGINAL recursive-root payload. BASE is
already sorted by the original root observer; extras retain original order. -/
def listPath : ListSlot → List Bool
 | .ordinaryBase => [true,true]
 | .numberedBase => [true,true,true,false]
 | .numberedExtras => [true,true,true,true]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDefinitions
