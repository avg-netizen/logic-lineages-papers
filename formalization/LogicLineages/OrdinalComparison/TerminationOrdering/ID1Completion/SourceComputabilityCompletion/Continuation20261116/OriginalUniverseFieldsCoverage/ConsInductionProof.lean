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
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsInductionProof
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
    (raw typ left right leftType rightType : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ left right)))
    (ho : Nonempty (Derivation body Delta (observations n arity H true raw xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hal : Nonempty (Derivation body Delta (accepted n arity H false leftType left (xs 6) (xs 2))))
    (har : Nonempty (Derivation body Delta (accepted n arity H true rightType right (xs 6) (xs 2))))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (xs 5) typ rightType)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n true raw xs)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (OriginalCodeBoundsConstructors.BinaryQueriesProof.queries n true) ![left,right] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![left,right] i).relabel j) = ![left.relabel j,right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hlb,hlp,hrb,hrp,hmax,hcanonical⟩ := OriginalCodeBoundsConstructors.BinaryQueriesProof.recover n true
    (left.relabel j) (right.relabel j) ys hq
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  have halj := renameInto hal j Theta hj
  have harj := renameInto har j Theta hj
  have htj := renameInto ht j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph3Rename] at hcj
  rw [ResultSyntaxProof.observationsRename] at hoj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj htj
  change Nonempty (Derivation body Theta
    ((OriginalUniverseDecoderInternalAcceptance.TermAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) leftType left (xs 6) (xs 2)).relabel j)) at halj
  rw [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] at halj
  change Nonempty (Derivation body Theta
    ((OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) rightType right (xs 6) (xs 2)).relabel j)) at harj
  rw [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.argumentsAcceptedRename] at harj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hlength := ObservationPartsProof.length n arity H true _ _ hoj
  have hlf := ChildFrameProof.child n arity H true false (raw.relabel j) (left.relabel j)
    (leftType.relabel j) ((xs 6).relabel j) ((xs 7).relabel j) (ys 0) (ys 1) (ys 2)
    (fun i => (xs i).relabel j) hoj halj hlength hlb hlp
  have hrf := ChildFrameProof.child n arity H true true (raw.relabel j) (right.relabel j)
    (rightType.relabel j) ((xs 6).relabel j) ((xs 7).relabel j) (ys 3) (ys 4) (ys 5)
    (fun i => (xs i).relabel j) hoj harj hlength hrb hrp
  have hd := OriginalTypedEnumerationDepthBound.DescentProof.cons
    (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) hcj
  have hil := ChildInductionProof.atChild n arity H false (raw.relabel j) (left.relabel j) _ ihj (andLeft hd) hlf
  have hir := ChildInductionProof.atChild n arity H true (raw.relabel j) (right.relabel j) _ ihj (andRight hd) hrf
  exact ConsCoreProof.atValues n arity H (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j)
    (leftType.relabel j) (rightType.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7)
    (fun i => (xs i).relabel j) hcj hoj hmj hlb hlp hrb hrp hmax hcanonical htj hil hir

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsInductionProof
