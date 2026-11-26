module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual frontier membership and successful recombination against the SAME old
association table imply first-match coverage in the literal stage output. -/
def InternalCoverage : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2) (G : Program 3)
    (frontier query old param deps answers value out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier query)) →
  Nonempty (Derivation body Delta (graph2 D deps query param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)) →
  Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Targets
