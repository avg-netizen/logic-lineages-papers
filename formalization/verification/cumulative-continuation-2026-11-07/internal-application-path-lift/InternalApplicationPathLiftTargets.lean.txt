module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalPathChecker InternalApplicationPathLift
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full internal path lifting from only local arithmetic edge preservation
and local invariant propagation, for the literal original application map.
Every certificate/output is a symbolic term and all hypotheses are retained. -/
def ActualInternalReflexivePathLift : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 3) (vertex invariant : Program 5),
  InvariantPreservation body edge invariant → EdgeCompatibility body edge vertex invariant →
  ∀ (α : Type) (Gamma : List (Formula α)) (ps : Parameters α)
    (x y code out other mapped : OTerm α),
  Nonempty (Derivation body Gamma (inputs edge vertex invariant false ps x y code out other mapped)) →
  Nonempty (Derivation body Gamma (pathGraph edge out other mapped))

/-- The positive checker keeps its literal rejection of nil. The theorem
preserves positive acceptance using the same concrete mapper and local edge
premises; no semantic path-lifting theorem is an internal premise. -/
def ActualInternalPositivePathLift : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 3) (vertex invariant : Program 5),
  InvariantPreservation body edge invariant → EdgeCompatibility body edge vertex invariant →
  ∀ (α : Type) (Gamma : List (Formula α)) (ps : Parameters α)
    (x y code out other mapped : OTerm α),
  Nonempty (Derivation body Gamma (inputs edge vertex invariant true ps x y code out other mapped)) →
  Nonempty (Derivation body Gamma (positiveGraph edge out other mapped))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathLiftTargets
