module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Every actual frontier node has a present first-match entry after the actual
argumentEntries stage. Outer Some zero is present; no value correctness assumed. -/
def InternalStageDomain : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (frontier old param table node found : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)) →
  Nonempty (Derivation body Delta (eqn found z).not)
/-- Domain completeness of the original successor graph at the literal
rank-subtraction frontier. Prior graph witnesses are eliminated internally. -/
def InternalSuccessorDomain : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index seed param depth frontier table node found : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)) →
  Nonempty (Derivation body Delta (eqn found z).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Targets
