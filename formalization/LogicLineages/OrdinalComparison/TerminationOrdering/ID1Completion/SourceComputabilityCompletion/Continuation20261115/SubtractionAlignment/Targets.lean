module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc eqn)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- Actual original subtraction [index,seed] computes seed-index. Under the
explicit arithmetic bound, its output is the additive complement, internally. -/
def InternalComplement : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index seed depth : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)) →
  Nonempty (Derivation body Delta (eqn (OrdinaryArithmetic.addTerm index depth) seed))
/-- Exact predecessor-stage depth alignment. The successor bound is explicit;
no saturation-at-zero case is silently identified with a positive complement. -/
def InternalPredecessorAlignment : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index seed depth : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (suc index) seed)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth (suc index) seed)) →
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract (suc depth) index seed))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.Targets
