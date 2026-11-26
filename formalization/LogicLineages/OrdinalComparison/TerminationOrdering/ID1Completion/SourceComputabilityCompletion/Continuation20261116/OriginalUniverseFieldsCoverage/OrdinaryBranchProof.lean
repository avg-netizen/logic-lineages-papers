module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ModeChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.HeadCoverageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.OrdinaryQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryBranchProof
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
    (raw head child symbols : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head child)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols (xs 0) (xs 1))))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have hh := HeadCoverageProof.ordinary n arity H raw head child symbols xs hc ho hs
  have hm := andLeft hh
  have hv := andRight hh
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases
    (OriginalTypedEnumerationDepthBound.OrdinaryQueryProof.queries H) ![head,child] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![head,child] i).relabel j) = ![head.relabel j,child.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨hpayload,hsignature,hfields⟩ := OriginalTypedEnumerationDepthBound.OrdinaryQueryProof.recover H
    (head.relabel j) (child.relabel j) ys hq
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  have hvj := renameInto hv j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [graph2Rename] at hcj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  rw [OriginalEnumerationFields.OrdinaryProof.allowedRename] at hmj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hpair := OriginalTypedEnumerationDepthBound.PayloadProof.ordinary
    (raw.relabel j) (head.relabel j) (child.relabel j) (ys 0) hcj hpayload
  have hchild := ModeChildrenProof.ordinaryChildren H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) (raw.relabel j) (ys 0) (head.relabel j)
    (child.relabel j) (ys 1) (ys 2) (ys 3) ((xs 5).relabel j) ((xs 6).relabel j) ((xs 2).relabel j)
    hpair hpayload hsignature hfields (ObservationPartsProof.admission n arity H false _ _ hoj)
  exact OrdinaryInductionProof.step n arity H (raw.relabel j) (head.relabel j) (child.relabel j)
    (ys 3) ((xs 6).relabel j) (fun i => (xs i).relabel j) hcj hoj hmj hvj hchild
    (ObservationPartsProof.length n arity H false _ _ hoj) ihj

theorem atConstructor (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw head child : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head child)))
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
  rw [graph2Rename] at hcj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  exact atSymbols n arity H (raw.relabel j) (head.relabel j) (child.relabel j) symbols
    (fun i => (xs i).relabel j) hcj hoj hs ihj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryBranchProof
