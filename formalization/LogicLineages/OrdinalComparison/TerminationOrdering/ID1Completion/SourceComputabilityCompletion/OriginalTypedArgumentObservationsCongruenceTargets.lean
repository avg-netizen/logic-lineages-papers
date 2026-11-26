module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors OriginalTypedArgumentObservationsCongruence
open OriginalTypedArgumentObservations OriginalUniverseDecoderInternalFuelNumericSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Generic parameter-preserving original primitive iteration; only the
explicit internal agreement of its transitions is assumed. -/
def IterationCongruence : Prop := ∀ (R S : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (count initial parameter left right : OTerm alpha),
 Nonempty (Derivation body Delta ((Agreement R S parameter ⊓
 (repeatGraph R left count initial parameter ⊓ repeatGraph S right count initial parameter)).imp (equal left right)))
def StepCongruence : Prop := ∀ (R S : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (parameter : OTerm alpha),
 Nonempty (Derivation body Delta ((Agreement R S parameter).imp
   (Agreement (walkStep R) (walkStep S) parameter)))
def ArgumentCongruence : Prop := ∀ (R S : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (raw parameter left right : OTerm alpha),
 Nonempty (Derivation body Delta ((Agreement R S parameter ⊓
 (graph2 (argumentObservations R) left raw parameter ⊓
  graph2 (argumentObservations S) right raw parameter)).imp (equal left right)))
def ArgumentIff : Prop := ∀ (R S : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (raw parameter out : OTerm alpha),
 Nonempty (Derivation body Delta ((Agreement R S parameter).imp
 ((graph2 (argumentObservations R) out raw parameter).iff
  (graph2 (argumentObservations S) out raw parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceTargets
