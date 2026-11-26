module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedTagProof
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

theorem numbered (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) raw)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases raw _ ht
  intro beta j Theta label head recorded base types extras hj hc
  rw [ResultSyntaxProof.resultRename]
  have hoj := renameInto ho j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact NumberedBranchProof.atConstructor n arity H (raw.relabel j) label head recorded base types extras
    (fun i => (xs i).relabel j) hc hoj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedTagProof
