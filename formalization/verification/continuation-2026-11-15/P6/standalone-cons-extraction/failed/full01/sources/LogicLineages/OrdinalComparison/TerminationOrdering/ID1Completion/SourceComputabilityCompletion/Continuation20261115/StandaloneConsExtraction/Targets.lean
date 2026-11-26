module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114

/-- Exact original cons extraction recurrence. The tail is an independent actual
extract call; previous-table alignment and equality are internal proof duties.
No typedness or head-cache value assumption is supplied. -/
def InternalConsEquation : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tau head tail param tailValue value : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)) →
  (Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) ↔
   Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))

/-- Standalone successful cons extraction preserves the original pair/list coding.
Some empty entries and failure zero remain distinct. -/
def InternalConsSuccess : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tau head tail param tailEntries entry listCode : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc listCode) raw param))

/-- An actual failing standalone tail yields actual failure, not a missing cache. -/
def InternalConsFailure : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tau head tail param : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract z tail param)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract z raw param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.Targets
