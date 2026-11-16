module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaClosureProof
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

theorem atChild (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw domain child childType extended childPair childSize childLabel : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) domain)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) childPair child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPair childSize childLabel)))
    (hchild : Nonempty (Derivation body Delta (result n false child
      (ChildFrameProof.frame xs childType extended (suc (xs 7)) childPair childSize childLabel)))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing
    (Fin.cons (suc childSize) (Fin.cons childLabel Fin.elim0)) _
  intro beta j Theta canonical hj hk
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename,sucRelabel] at hk
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hchildj := renameInto hchild j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcj hmj hbj hpj
  rw [ResultSyntaxProof.observationsRename] at hoj
  rw [ResultSyntaxProof.resultRename,ChildFrameSyntaxProof.frameRename,sucRelabel] at hchildj
  exact LambdaCoreProof.atPair n arity H (raw.relabel j) (domain.relabel j) (child.relabel j)
    (childType.relabel j) (extended.relabel j) (childPair.relabel j) (childSize.relabel j)
    (childLabel.relabel j) canonical (fun i => (xs i).relabel j) hcj hoj hmj hbj hpj hk hchildj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaClosureProof
