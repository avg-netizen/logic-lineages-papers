module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal final rank-subtraction stage: no dependency coverage or old-table
coherence is needed for an actually empty dependency list. -/
def InternalLeaf : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (R D : Program 2) (G : Program 3) (seed param value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 D (numeral 0) seed param)) →
  Nonempty (Derivation body Delta (graph3 G (suc value) seed (numeral 0) param)) →
  Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param))

/-- Actual argsNil dependency and recombination, not calibrated oracle facts. -/
def InternalNilSuppliers : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw answers param : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) →
  Nonempty (Derivation body Delta
    (graph2 ArgumentEntriesRecursor.dependency (numeral 0) raw param ⊓
     graph3 ArgumentEntriesRecursor.layer (numeral 2) raw answers param))

/-- The original actual extraction is Some [] = 1, not None = 0. -/
def InternalNilExtraction : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw param : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (numeral 1) raw param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Targets
