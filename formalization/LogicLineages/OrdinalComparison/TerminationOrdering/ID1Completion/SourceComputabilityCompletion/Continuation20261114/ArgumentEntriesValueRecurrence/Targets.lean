module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesValueRecurrence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- A cached value is the actual original recombination of this same old table's
mapped answers, not merely a present key. No cross-root equation is asserted. -/
def InternalStageValue : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (frontier old param table node deps answers value : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table node)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.layer (suc value) node answers param))
/-- Actual original graph successor at literal rank(seed)-index frontier. -/
def InternalSuccessorValue : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index seed param depth frontier old table node deps answers value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old index seed param)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) table node)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.layer (suc value) node answers param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesValueRecurrence.Targets
