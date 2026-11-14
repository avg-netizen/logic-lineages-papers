module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every live field is supplied by a concrete AST. Fillers at answer slots are
ignored by the existing actual lookup installation. V remains the explicit decoder guard. -/
def layer (n : Nat) (arity : Fin n → Nat) (V : Program 3) : Program 3 :=
  HeadMoveFields.layer n arity (fun _ => .composition .zero (fun i => Fin.elim0 i)) V
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer
