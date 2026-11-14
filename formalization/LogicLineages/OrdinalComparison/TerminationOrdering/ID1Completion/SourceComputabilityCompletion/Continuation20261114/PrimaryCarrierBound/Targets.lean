module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership
/-- Every actual iterate member lies in the unchanged initial list or the
fixed pool. Count is an arbitrary arithmetic term; E is genuinely generic. -/
def IterationCarrier : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (count pool initial parameter out candidate : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.iterate E) out count pool initial parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) →
  Nonempty (Derivation body Delta (inCarrier initial pool candidate))
/-- Actual singleton seed, with genuine internal equality or pool membership,
not an externally extracted disjunction or decoded standard-natural witness. -/
def RunCarrier : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (count pool seed parameter out candidate : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.run E) out count pool seed parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) →
  Nonempty (Derivation body Delta
    (eqn candidate seed ⊔ graph2 contains (numeral 1) pool candidate))
/-- Explicit seed-in-pool hypothesis, not an unpaid assertion about selected
vertices: the actual output is internally included in this very same pool. -/
def RunIncludedInPool : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (count pool seed parameter out : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.run E) out count pool seed parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool seed)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included out pool))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.Targets
