module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Negated inclusion yields an INTERNAL existential pool witness for strict
potential decrease, not metalevel extraction or failure of proof search. -/
def InternalGrowthWitness : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (pool before after parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) after pool before parameter)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included after before).not) →
  Nonempty (Derivation body Delta (growthWitness pool before after))
/-- Stability means equality of membership, not equality of duplicate-bearing
list codes. The forward inclusion is already provided by actual expansion. -/
def SuccessorStability : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (pool before after next parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) after pool before parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) next pool after parameter)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included after before)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included next after))
/-- Genuine internal persistence for an arbitrary symbolic iteration count.
The fixed point is membership-only; no equal-output-code assumption is used. -/
def IterationStability : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (count pool initial first parameter out : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) first pool initial parameter)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included first initial)) →
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.iterate E) out count pool initial parameter)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included out initial))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.Targets
