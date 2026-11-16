module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryTagsProof
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

theorem application (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 2) raw)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases raw _ ht
  intro beta j Theta domain left right hj hc
  rw [ResultSyntaxProof.resultRename]
  have hoj := renameInto ho j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact ApplicationBranchProof.atConstructor n arity H (raw.relabel j) domain left right
    (fun i => (xs i).relabel j) hc hoj ihj

theorem cons (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 7) raw)))
    (ho : Nonempty (Derivation body Delta (observations n arity H true raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n true raw xs)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ ht
  intro beta j Theta domain head tail hj hc
  rw [ResultSyntaxProof.resultRename]
  have hoj := renameInto ho j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact ConsBranchProof.atConstructor n arity H (raw.relabel j) domain head tail
    (fun i => (xs i).relabel j) hc hoj ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryTagsProof
