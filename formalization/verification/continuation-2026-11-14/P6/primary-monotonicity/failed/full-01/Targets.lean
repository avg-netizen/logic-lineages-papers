module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine internal witness transfer for the actual any fold. -/
def AnyMonotonicity : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (left right candidate parameter : OTerm alpha),
  Nonempty (Derivation body Delta (included left right)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.anyEdge E) (numeral 1) left candidate parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.anyEdge E) (numeral 1) right candidate parameter))
/-- Same fixed pool, parameter and actual E; only reached input varies.
Outputs are literal original append/filter results, not deduplicated lists. -/
def ExpansionMonotonicity : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (pool left right parameter leftOut rightOut : OTerm alpha),
  Nonempty (Derivation body Delta (included left right)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) leftOut pool left parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) rightOut pool right parameter)) →
  Nonempty (Derivation body Delta (included leftOut rightOut))
/-- Relational arithmetic induction at an arbitrary symbolic count, not an
external Nat induction. No cutoff closure or original-edge correctness premise. -/
def IterationMonotonicity : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (count pool left right parameter leftOut rightOut : OTerm alpha),
  Nonempty (Derivation body Delta (included left right)) →
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.iterate E) leftOut count pool left parameter)) →
  Nonempty (Derivation body Delta
    (graph4 (PrimaryIteration.iterate E) rightOut count pool right parameter)) →
  Nonempty (Derivation body Delta (included leftOut rightOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.Targets
