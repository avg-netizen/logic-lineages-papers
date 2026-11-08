module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationEndpointGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationEndpointGuardTargets
open Source InternalApplicationStepPeel
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The exact existing leaf is primitive recursive on all natural five-tuples.
There is no subtype-closure, successful-decoding or universe premise. -/
def ActualOriginalEndpointPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
    Primrec (endpointValue n arity symbols S Gamma)

/-- One original Program5 per fixed signature, window and Gamma is calibrated
on every input, including malformed type/packed codes and rejected universes.
This existential does not expose a structural decoder implementation. -/
def ActualOriginalEndpointProgramExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
    ∃ endpoint : Program 5, EndpointCalibrated n arity symbols S Gamma endpoint

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationEndpointGuardTargets
