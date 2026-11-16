module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypeSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.RootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArrowObservationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsBranchProof
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
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ left right)))
    (ho : Nonempty (Derivation body Delta (observations n arity H true raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n true raw xs)) := by
  apply OriginalTypedEnumerationDepthBound.ArrowObservationsProof.cases (xs 5) _
  intro beta j Theta requested tailTypes hj hfields
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph3Rename] at hcj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have ha := ObservationPartsProof.admission n arity H true _ _ hoj
  have hi := OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (raw.relabel j) (typ.relabel j) (left.relabel j)
    (right.relabel j) ((xs 5).relabel j) requested tailTypes ((xs 6).relabel j) ((xs 2).relabel j) hcj hfields
  have hf := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice ha)
  have hleft := andLeft (andRight (andRight (show Nonempty (Derivation body Theta _) from ⟨hf⟩)))
  have hright := andRight (andRight (andRight (show Nonempty (Derivation body Theta _) from ⟨hf⟩)))
  have hroot := OriginalUniverseDomainCoverage.RootProof.requestedType H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (typ.relabel j) (left.relabel j)
    ((xs 6).relabel j) ((xs 2).relabel j) hleft
  have hm := OriginalUniverseDomainCoverage.MemberProof.membership n (typ.relabel j) ((xs 2).relabel j)
    ((xs 3).relabel j) hroot (MetadataProof.typesAt ((xs 0).relabel j) ((xs 1).relabel j) ((xs 2).relabel j)
      ((xs 3).relabel j) (ObservationPartsProof.context n arity H true _ _ hoj)
      (ObservationPartsProof.types n arity H true _ _ hoj))
  have htypes := TypeSpineProof.atCons H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (raw.relabel j) (typ.relabel j) (left.relabel j)
    (right.relabel j) ((xs 5).relabel j) requested tailTypes ((xs 6).relabel j) ((xs 2).relabel j) hcj hfields ha
  exact ConsInductionProof.step n arity H (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j)
    (typ.relabel j) tailTypes (fun i => (xs i).relabel j) hcj hoj hm hleft hright htypes ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsBranchProof
