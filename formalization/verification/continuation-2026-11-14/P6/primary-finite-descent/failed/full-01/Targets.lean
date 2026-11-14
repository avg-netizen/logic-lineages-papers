module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine internal alternative: the actual expansion is membership-stable
or its actual uncovered-entry potential strictly drops. -/
def StepAlternative : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (pool before after parameter beforeCount afterCount : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) after pool before parameter)) →
  Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count beforeCount pool before)) →
  Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count afterCount pool after)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included after before ⊔
    arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula afterCount beforeCount)))
/-- Arbitrary symbolic elapsed count; actual initial/current potentials and
actual next expansion. The disjunctive invariant must be proved internally. -/
def IterationBudget : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (elapsed pool initial parameter out next initialRemaining remaining : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.iterate E) out elapsed pool initial parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) next pool out parameter)) →
  Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count initialRemaining pool initial)) →
  Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count remaining pool out)) →
  Nonempty (Derivation body Delta (budget elapsed initialRemaining remaining out next))
/-- Stabilization at the ACTUAL literal pool length, not a substituted
numeric-code bound or a new fuel. This does not assume opaque C = length(P). -/
def LiteralLengthCutoff : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (size pool initial parameter out next : OTerm alpha),
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size pool)) →
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.iterate E) out size pool initial parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) next pool out parameter)) →
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included next out))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.Targets
