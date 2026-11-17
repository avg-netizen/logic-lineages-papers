module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedInductionProof
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

theorem step (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw rootLabel head typ left types right leftType : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hh : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n (xs 4) head)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hal : Nonempty (Derivation body Delta (accepted n arity H true leftType left (xs 6) (xs 2))))
    (har : Nonempty (Derivation body Delta (accepted n arity H true types right (xs 6) (xs 2))))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (OriginalCodeBoundsConstructors.NumberedQueriesProof.queries n) ![rootLabel,left,right] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![rootLabel,left,right] i).relabel j) = ![rootLabel.relabel j,left.relabel j,right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hlb,hlp,hrb,hrp,hm0,hm1,hcanonical⟩ := OriginalCodeBoundsConstructors.NumberedQueriesProof.recover n
    (rootLabel.relabel j) (left.relabel j) (right.relabel j) ys hq
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hhj := renameInto hh j Theta hj
  have hvj := renameInto hv j Theta hj
  have hmj := renameInto hm j Theta hj
  have halj := renameInto hal j Theta hj
  have harj := renameInto har j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [programRename] at hcj
  have hcx : (fun i => (![rootLabel,head,typ,left,types,right] i).relabel j) =
      ![rootLabel.relabel j,head.relabel j,typ.relabel j,left.relabel j,types.relabel j,right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hcx] at hcj
  rw [ResultSyntaxProof.observationsRename] at hoj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hvj hmj
  rw [OriginalEnumerationFields.NumberedProof.headAllowedRename] at hhj
  change Nonempty (Derivation body Theta
    ((OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) leftType left (xs 6) (xs 2)).relabel j)) at halj
  rw [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.argumentsAcceptedRename] at halj
  change Nonempty (Derivation body Theta
    ((OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) types right (xs 6) (xs 2)).relabel j)) at harj
  rw [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.argumentsAcceptedRename] at harj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hlength := ObservationPartsProof.length n arity H false _ _ hoj
  have hlf := ChildFrameProof.child n arity H false true (raw.relabel j) (left.relabel j)
    (leftType.relabel j) ((xs 6).relabel j) ((xs 7).relabel j) (ys 0) (ys 1) (ys 2)
    (fun i => (xs i).relabel j) hoj halj hlength hlb hlp
  have hrf := ChildFrameProof.child n arity H false true (raw.relabel j) (right.relabel j)
    (types.relabel j) ((xs 6).relabel j) ((xs 7).relabel j) (ys 3) (ys 4) (ys 5)
    (fun i => (xs i).relabel j) hoj harj hlength hrb hrp
  have hd := OriginalTypedEnumerationDepthBound.DescentProof.numbered (raw.relabel j) (rootLabel.relabel j)
    (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j) hcj
  have hil := ChildInductionProof.atChild n arity H true (raw.relabel j) (left.relabel j) _ ihj (andLeft hd) hlf
  have hir := ChildInductionProof.atChild n arity H true (raw.relabel j) (right.relabel j) _ ihj (andRight hd) hrf
  exact NumberedCoreProof.atValues n arity H (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j)
    (left.relabel j) (types.relabel j) (right.relabel j) (leftType.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 8) (ys 9)
    (fun i => (xs i).relabel j) hcj hoj hhj hvj hmj hlb hlp hrb hrp hm0 hm1 hcanonical hil hir

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedInductionProof
