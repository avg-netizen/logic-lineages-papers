module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.KnownProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.DispatchProof
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

theorem observed (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw)))
    (ho : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (result n arguments raw xs)) := by
  apply OriginalTypedDecoderTransportTagSupportProof.rawTagCases raw _
  · intro beta j Theta i payload hj ht hp
    rw [ResultSyntaxProof.resultRename]
    have hoj := renameInto ho j Theta hj
    have ihj := renameInto ih j Theta hj
    rw [ResultSyntaxProof.observationsRename] at hoj
    rw [InductionSyntaxProof.belowRawRename] at ihj
    cases arguments
    · exact KnownProof.termKnown n arity H i (raw.relabel j) payload (fun i => (xs i).relabel j) hoj ihj ht hp
    · exact KnownProof.argumentsKnown n arity H i (raw.relabel j) payload (fun i => (xs i).relabel j) hoj ihj ht hp
  · intro beta j Theta tag payload hj hp hu
    rw [ResultSyntaxProof.resultRename]
    have hoj := renameInto ho j Theta hj
    rw [ResultSyntaxProof.observationsRename] at hoj
    have ha := ObservationPartsProof.admission n arity H arguments _ _ hoj
    cases arguments
    · exact OriginalUniverseDecoderTransportRejectedProof.unknown H (OriginalUniverseDomainCoverage.member n)
        (OriginalGuardedHeadSourceCoverage.window n arity) false (raw.relabel j) tag payload ((xs 5).relabel j)
        ((xs 6).relabel j) ((xs 2).relabel j) _ hp hu ha
    · exact OriginalUniverseDecoderTransportRejectedProof.unknown H (OriginalUniverseDomainCoverage.member n)
        (OriginalGuardedHeadSourceCoverage.window n arity) true (raw.relabel j) tag payload ((xs 5).relabel j)
        ((xs 6).relabel j) ((xs 2).relabel j) _ hp hu ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.DispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.DispatchProof
