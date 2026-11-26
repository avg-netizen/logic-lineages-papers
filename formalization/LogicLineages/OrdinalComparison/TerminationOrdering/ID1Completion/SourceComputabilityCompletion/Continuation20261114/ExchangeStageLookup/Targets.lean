module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- A successful first frontier node is the first association entry, irrespective
of duplicate nodes later in the frontier. No total-table coherence is assumed. -/
def InternalHeadLookup : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2) (G : Program 3)
    (frontier node tail old param deps answers value out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)) →
  Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out node))

/-- A genuinely absent recombination is omitted; it does not insert Some zero. -/
def InternalSkippedLookup : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2) (G : Program 3)
    (frontier node tail old param deps answers out rest key result : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)) →
  Nonempty (Derivation body Delta (graph3 G z node answers param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)) →
  (Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)))

/-- A successful nonmatching head preserves literal first-match lookup in the
actual tail stage. Distinctness is an object-language premise, not proof search. -/
def InternalDistinctLookup : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2) (G : Program 3)
    (frontier node tail old param deps answers value out rest key result : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)) →
  Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)) →
  Nonempty (Derivation body Delta (eqn node key).not) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)) →
  (Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.Targets
