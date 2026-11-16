module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.SymbolsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationPartsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.OrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.NumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.HeadCoverageProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem ordinary (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw head child symbols : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head child)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols (xs 0) (xs 1)))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n (xs 4) head ⊓
      graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)) := by
  have hcontext := ObservationPartsProof.context n arity H false raw xs ho
  have htypes := ObservationPartsProof.types n arity H false raw xs ho
  have hsource := OriginalGuardedHeadSourceCoverage.OrdinaryProof.internalOrdinaryHead n arity H body alpha Delta
    raw head child (xs 5) (xs 6) (xs 2) symbols (xs 3) hc
    (ObservationPartsProof.admission n arity H false raw xs ho)
    (SymbolsProof.symbolsAt (xs 0) (xs 1) (xs 2) symbols hcontext hs)
    (MetadataProof.typesAt (xs 0) (xs 1) (xs 2) (xs 3) hcontext htypes)
    (ObservationPartsProof.closed n arity H false raw xs ho)
  exact andIntro (OriginalSourceHeadsFieldsBridge.Proof.internalHeadAllowed n arity body alpha Delta
    (xs 0) (xs 1) head symbols (xs 3) (xs 4) hs htypes
    (ObservationPartsProof.heads n arity H false raw xs ho) hsource) (andLeft hsource)

theorem numbered (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw label head recorded base extraTypes extra symbols : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,recorded,base,extraTypes,extra])))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols (xs 0) (xs 1)))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n (xs 4) head ⊓
      graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)) := by
  have hcontext := ObservationPartsProof.context n arity H false raw xs ho
  have htypes := ObservationPartsProof.types n arity H false raw xs ho
  have hsource := OriginalGuardedHeadSourceCoverage.NumberedProof.internalNumberedHead n arity H body alpha Delta
    raw label head recorded base extraTypes extra (xs 5) (xs 6) (xs 2) symbols (xs 3) hc
    (ObservationPartsProof.admission n arity H false raw xs ho)
    (SymbolsProof.symbolsAt (xs 0) (xs 1) (xs 2) symbols hcontext hs)
    (MetadataProof.typesAt (xs 0) (xs 1) (xs 2) (xs 3) hcontext htypes)
    (ObservationPartsProof.closed n arity H false raw xs ho)
  exact andIntro (OriginalSourceHeadsFieldsBridge.Proof.internalHeadAllowed n arity body alpha Delta
    (xs 0) (xs 1) head symbols (xs 3) (xs 4) hs htypes
    (ObservationPartsProof.heads n arity H false raw xs ho) hsource) (andLeft hsource)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.HeadCoverageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.HeadCoverageProof
