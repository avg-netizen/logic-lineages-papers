module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Inputs [node,old association graph,parameter]. D returns the literal ordered
dependency list, including duplicates. Missing old keys are omitted by mapGraph. -/
def dependencies (D : Program 2) : Program 3 := .composition D ![.projection 0,.projection 2]
def answers (D : Program 2) : Program 3 := .composition ExchangeMapGraph.mapGraph
  ![dependencies D,.projection 1]
def nodeAnswer (D : Program 2) (G : Program 3) : Program 3 := .composition G
  ![.projection 0,answers D,.projection 2]
/-- Inputs [node,recursive filtered tail,old graph,parameter]. None=0;
some value=successor value. Omit None, prepend exactly (node,value) otherwise. -/
def stepAnswer (D : Program 2) (G : Program 3) : Program 4 :=
  .composition (nodeAnswer D G) ![.projection 0,.projection 2,.projection 3]
def entry (D : Program 2) (G : Program 3) : Program 4 :=
  .composition InternalPairing.pairing ![.projection 0,
    .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => stepAnswer D G)]
def step (D : Program 2) (G : Program 3) : Program 4 :=
  InternalAcceptance.branch (stepAnswer D G) (.projection 1)
    (.composition InternalListCodec.consCode ![entry D G,.projection 1])
/-- Literal filterMap stage of nat_omega_rec'. Inputs [frontier,old graph,parameter].
It does not accumulate old entries; graph recursion and frontier construction remain separate. -/
def stage (D : Program 2) (G : Program 3) : Program 3 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 2) (step D G)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage
