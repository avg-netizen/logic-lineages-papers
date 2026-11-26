module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypeSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.RootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArrowObservationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationBranchProof
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

open InternalAdditionLawsProof (add)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem atConstructor (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw typ left right : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw typ left right)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply InternalAcceptanceSupportProof.programCases InternalListCodec.consCode
    (Fin.cons typ (Fin.cons (xs 5) Fin.elim0)) _
  intro beta j Theta arrow hj hfields
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hfields
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph3Rename] at hcj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have ha := ObservationPartsProof.admission n arity H false _ _ hoj
  have hi := OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (raw.relabel j) (typ.relabel j) (left.relabel j)
    (right.relabel j) ((xs 5).relabel j) arrow ((xs 6).relabel j) ((xs 2).relabel j) hcj hfields
  have hf := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice ha)
  have hleft := andLeft (andRight (show Nonempty (Derivation body Theta _) from ⟨hf⟩))
  have hright := andRight (andRight (show Nonempty (Derivation body Theta _) from ⟨hf⟩))
  have hroot := OriginalUniverseDomainCoverage.RootProof.requestedType H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (typ.relabel j) (right.relabel j)
    ((xs 6).relabel j) ((xs 2).relabel j) hright
  have hm := OriginalUniverseDomainCoverage.MemberProof.membership n (typ.relabel j) ((xs 2).relabel j)
    ((xs 3).relabel j) hroot (MetadataProof.typesAt ((xs 0).relabel j) ((xs 1).relabel j) ((xs 2).relabel j)
      ((xs 3).relabel j) (ObservationPartsProof.context n arity H false _ _ hoj)
      (ObservationPartsProof.types n arity H false _ _ hoj))
  exact ApplicationInductionProof.step n arity H (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j)
    arrow (typ.relabel j) (fun i => (xs i).relabel j) hcj hoj hm hleft hright ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationBranchProof
