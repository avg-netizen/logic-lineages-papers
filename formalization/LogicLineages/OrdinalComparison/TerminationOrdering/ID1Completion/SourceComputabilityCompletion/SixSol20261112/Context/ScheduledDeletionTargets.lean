module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The genuine scheduled deletion cell at original position arity+cutoff.
Raw deletion lookup, actual decoration and actual scalar-from-job computation
are the only operational premises. Inherited role/type, erased packed input,
deleted context/window and observation wiring must all be recovered internally.
No source validity, covariance, whole result invariant or fixed-point premise. -/
def ActualCell : Prop := ∀ (Q : Program 2) (arity : Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw parameter jobs count cutoff rawCell annotated value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count jobs)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell cutoff jobs)) →
  Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate annotated
    (OriginalInternalIndexedPrefixCasesTargets.bump arity cutoff) (numeral 0) typ raw rawCell)) →
  Nonempty (Derivation body Delta (graph1 (ScheduledDeletionDefinitions.scalarFromJob Q) value annotated)) →
  Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionTargets
