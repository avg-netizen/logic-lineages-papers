module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Iteration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- Only the actual runtime output is quantified here. Every original environment
and initial-reached parameter stays free and is transported by the binding laws. -/
def matrix {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter rootTypeRef boundsRef : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity))
    (.var (.inr 0)) (count.relabel Sum.inl) (pool.relabel Sum.inl)
    (reached.relabel Sum.inl) (parameter.relabel Sum.inl)).imp
      ((allAccepted n arity (reached.relabel Sum.inl) (rootTypeRef.relabel Sum.inl) (boundsRef.relabel Sum.inl)).imp
        (allAccepted n arity (.var (.inr 0)) (rootTypeRef.relabel Sum.inl) (boundsRef.relabel Sum.inl)))
def AtCount {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter rootTypeRef boundsRef : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n arity count pool reached parameter rootTypeRef boundsRef)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Iteration
