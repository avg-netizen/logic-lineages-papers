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
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryInductionProof
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

theorem step (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw head child childType extended : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head child)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hm : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n (xs 4) head)))
    (hh : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)))
    (ha : Nonempty (Derivation body Delta (accepted n arity H true childType child extended (xs 2))))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length (xs 7) extended)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply ChildObservationsProof.cases n child _
  intro beta j Theta pair size label hj hb hp
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  have hhj := renameInto hh j Theta hj
  have haj := renameInto ha j Theta hj
  have hlj := renameInto hl j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hcj hhj hlj
  rw [OriginalEnumerationFields.OrdinaryProof.allowedRename] at hmj
  rw [ResultSyntaxProof.observationsRename] at hoj
  change Nonempty (Derivation body Theta
    ((OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) childType child extended (xs 2)).relabel j)) at haj
  rw [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.argumentsAcceptedRename] at haj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  have hf := ChildFrameProof.child n arity H false true (raw.relabel j) (child.relabel j)
    (childType.relabel j) (extended.relabel j) ((xs 7).relabel j) pair size label
    (fun i => (xs i).relabel j) hoj haj hlj hb hp
  have hi := ChildInductionProof.atChild n arity H true (raw.relabel j) (child.relabel j)
    (ChildFrameProof.frame (fun i => (xs i).relabel j) (childType.relabel j) (extended.relabel j)
      ((xs 7).relabel j) pair size label) ihj
    (OriginalTypedEnumerationDepthBound.DescentProof.ordinary _ _ _ hcj) hf
  exact OrdinaryClosureProof.atChild n arity H (raw.relabel j) (head.relabel j) (child.relabel j)
    (childType.relabel j) (extended.relabel j) pair size label (fun i => (xs i).relabel j) hcj hoj hmj hhj hb hp hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.OrdinaryInductionProof
