module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ModeChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.HeadCoverageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MemberTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedBranchProof
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

open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem atSymbols (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw rootLabel head typ left types right symbols : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols (xs 0) (xs 1))))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have hh := HeadCoverageProof.numbered n arity H raw rootLabel head typ left types right symbols xs hc ho hs
  have hm := andLeft hh
  have hv := andRight hh
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (OriginalTypedEnumerationDepthBound.OrdinaryQueryProof.queries H) ![head,left] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![head,left] i).relabel j) = ![head.relabel j,left.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨_,hsignature,hfields⟩ := OriginalTypedEnumerationDepthBound.OrdinaryQueryProof.recover H
    (head.relabel j) (left.relabel j) ys hq
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  have hvj := renameInto hv j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [programRename] at hcj
  have hcx : (fun i => (![rootLabel,head,typ,left,types,right] i).relabel j) =
      ![rootLabel.relabel j,head.relabel j,typ.relabel j,left.relabel j,types.relabel j,right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hcx] at hcj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  rw [OriginalEnumerationFields.NumberedProof.headAllowedRename] at hmj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hi := OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (raw.relabel j) (rootLabel.relabel j) (head.relabel j)
    (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j) (ys 1) (ys 2) (ys 3)
    ((xs 5).relabel j) ((xs 6).relabel j) ((xs 2).relabel j) hcj hsignature hfields
  have ha := ObservationPartsProof.admission n arity H false _ _ hoj
  have hf := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice ha)
  have hroot : Nonempty (Derivation body Theta (graph2 (OriginalUniverseDomainCoverage.member n) (numeral 1)
      ((xs 5).relabel j) ((xs 2).relabel j))) := ⟨Derivation.conjunctionLeft hf⟩
  have he : Nonempty (Derivation body Theta (equal (typ.relabel j) ((xs 5).relabel j))) :=
    andLeft (andRight (andRight (andRight (show Nonempty (Derivation body Theta _) from ⟨hf⟩))))
  rw [InternalControlGraphSupportProof.equalEqn] at he
  have hchildren := andRight (andRight (andRight (andRight (show Nonempty (Derivation body Theta _) from ⟨hf⟩))))
  have hmember := OriginalUniverseDomainCoverage.MemberProof.membership n ((xs 5).relabel j) ((xs 2).relabel j)
    ((xs 3).relabel j) hroot (MetadataProof.typesAt ((xs 0).relabel j) ((xs 1).relabel j) ((xs 2).relabel j)
      ((xs 3).relabel j) (ObservationPartsProof.context n arity H false _ _ hoj)
      (ObservationPartsProof.types n arity H false _ _ hoj))
  have hrecorded := MemberTransportProof.transport ((xs 3).relabel j) ((xs 5).relabel j) (typ.relabel j)
    ⟨symm (Classical.choice he)⟩ hmember
  exact NumberedInductionProof.step n arity H (raw.relabel j) (rootLabel.relabel j) (head.relabel j)
    (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j) (ys 3)
    (fun i => (xs i).relabel j) hcj hoj hmj hvj hrecorded (andLeft hchildren) (andRight hchildren) ihj

theorem atConstructor (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw rootLabel head typ left types right : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply InternalAcceptanceSupportProof.programCases OriginalClassCodes.symbols
    (Fin.cons (xs 0) (Fin.cons (xs 1) Fin.elim0)) _
  intro beta j Theta symbols hj hs
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hs
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [programRename] at hcj
  have hcx : (fun i => (![rootLabel,head,typ,left,types,right] i).relabel j) =
      ![rootLabel.relabel j,head.relabel j,typ.relabel j,left.relabel j,types.relabel j,right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hcx] at hcj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact atSymbols n arity H (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j)
    (left.relabel j) (types.relabel j) (right.relabel j) symbols (fun i => (xs i).relabel j) hcj hoj hs ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedBranchProof
