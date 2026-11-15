module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Present values, including zero, are retained. Missing values are not filled. -/
def InternalMapPresent : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (keys key tail entries value rest out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys key tail)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) entries key)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph rest tail entries)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value rest)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph out keys entries))

/-- Final stage of the original algorithm with ACTUAL previous graph and mapped
answers. This does not identify those answers with independent child evaluations. -/
def InternalFinalAnswers : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (R D : Program 2) (G : Program 3)
    (seed param rank old deps answers value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 R rank seed param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)) →
  Nonempty (Derivation body Delta (graph2 D deps seed param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)) →
  Nonempty (Derivation body Delta (graph3 G (suc value) seed answers param)) →
  Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param))

/-- Exact nonempty-spine step from actual original previous-table lookup facts.
The outer successor at lookup means Some; tail value itself is Some entries. -/
def InternalConsTable : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (raw tau head tail param old headValue tailEntries entry listCode : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)) →
  Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc headValue) old head)) →
  Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc (suc tailEntries)) old tail)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc listCode) raw param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.Targets
