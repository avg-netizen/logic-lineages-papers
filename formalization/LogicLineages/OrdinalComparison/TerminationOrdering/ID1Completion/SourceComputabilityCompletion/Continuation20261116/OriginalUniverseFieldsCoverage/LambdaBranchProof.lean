module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ModeChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.LambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LambdaQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaBranchProof
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

theorem atConstructor (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw domain child : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have hm := OriginalUniverseDomainCoverage.LambdaProof.internalLambdaDomain n H
    (OriginalGuardedHeadSourceCoverage.window n arity) body alpha Delta raw domain child (xs 5) (xs 6) (xs 2) (xs 3)
    hc (ObservationPartsProof.admission n arity H false raw xs ho)
    (MetadataProof.typesAt (xs 0) (xs 1) (xs 2) (xs 3)
      (ObservationPartsProof.context n arity H false raw xs ho)
      (ObservationPartsProof.types n arity H false raw xs ho))
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    OriginalTypedEnumerationDepthBound.LambdaQueryProof.queries ![domain,child,xs 5,xs 6] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![domain,child,xs 5,xs 6] i).relabel j) =
      ![domain.relabel j,child.relabel j,(xs 5).relabel j,(xs 6).relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hpayload,hext,hfields⟩ := OriginalTypedEnumerationDepthBound.LambdaQueryProof.recover
    (domain.relabel j) (child.relabel j) ((xs 5).relabel j) ((xs 6).relabel j) ys hq
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph2Rename] at hcj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hpair := OriginalTypedEnumerationDepthBound.PayloadProof.lambdaCode
    (raw.relabel j) (domain.relabel j) (child.relabel j) (ys 0) hcj hpayload
  have hchild := ModeChildrenProof.lambdaChildren H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (raw.relabel j) (ys 0) (domain.relabel j)
    (child.relabel j) ((xs 5).relabel j) (ys 2) (ys 3) ((xs 6).relabel j) (ys 1) ((xs 2).relabel j)
    hpair hpayload hfields hext (ObservationPartsProof.admission n arity H false _ _ hoj)
  have hlength := OriginalContextInsertionLengthProof.lengthCons (ys 1) (domain.relabel j)
    ((xs 6).relabel j) ((xs 7).relabel j) hext (ObservationPartsProof.length n arity H false _ _ hoj)
  exact LambdaInductionProof.step n arity H (raw.relabel j) (domain.relabel j) (child.relabel j)
    (ys 3) (ys 1) (fun i => (xs i).relabel j) hcj hoj hmj hchild hlength ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaBranchProof
