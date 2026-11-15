module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Every actual dependency of a current-frontier node is present in the
previous original table when its literal rank-subtraction depth is d+1.
No identification of its cached value with a standalone child call is made. -/
def InternalPreviousCoverage : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (index seed param depth frontier table node deps child found : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract (suc depth) index seed)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table child)) →
  Nonempty (Derivation body Delta (eqn found z).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Targets
