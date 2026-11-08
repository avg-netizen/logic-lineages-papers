module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalParameterizedPathChecker InternalParameterizedApplicationPathLift
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full internal reflexive path transport from local invariant propagation
and local edge compatibility. The original mapper is unchanged; source,
target, certificate and parameter are arbitrary symbolic terms. -/
def ActualInternalParameterizedReflexivePathLift : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 4) (vertex invariant : Program 5),
  InvariantPreservation body edge invariant → EdgeCompatibility body edge vertex invariant →
  ∀ (α : Type) (Gamma : List (Formula α)) (ps : Parameters α)
    (x y code out other mapped : OTerm α),
  Nonempty (Derivation body Gamma (inputs edge vertex invariant false ps x y code out other mapped)) →
  Nonempty (Derivation body Gamma (pathGraph edge out other mapped (ps 0)))

/-- Positive source acceptance yields a genuine original cons internally.
Its reflexive suffix is transported by the list induction, retaining the
same parameter and the exact supplied mapped output. No whole-path premise. -/
def ActualInternalParameterizedPositivePathLift : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 4) (vertex invariant : Program 5),
  InvariantPreservation body edge invariant → EdgeCompatibility body edge vertex invariant →
  ∀ (α : Type) (Gamma : List (Formula α)) (ps : Parameters α)
    (x y code out other mapped : OTerm α),
  Nonempty (Derivation body Gamma (inputs edge vertex invariant true ps x y code out other mapped)) →
  Nonempty (Derivation body Gamma (positiveGraph edge out other mapped (ps 0)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftTargets
