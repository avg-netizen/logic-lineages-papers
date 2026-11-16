module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseTaggedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseHeadTaggedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseObservedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open MeaningSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem atFields (n : Nat) (xs : Fin 7 → OTerm alpha) (fuel raw tag payload first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (ha : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 5) (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3))))
    (ho : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 6) (suc (xs 4)) fuel (xs 0) (xs 1) (xs 2) (xs 3))))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw (xs 4) (suc fuel) (xs 0) (xs 1) (xs 2) (xs 3)))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.alternatives n xs raw)) := by
  apply GuardChoiceProof.eliminate n tag payload first second head _ ha
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have hc := variableConstructorValue raw payload (GuardPairProof.pairLiteral raw tag payload 0 (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact (orLeft (Classical.choice (ReverseLeafProof.variableCode n (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3) raw payload hc (withHyp h _))))
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have ht := GuardPairProof.tagLiteral raw tag payload 1 (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact (orRight (orLeft (Classical.choice (ReverseTaggedProof.lambdaCase n (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3) (xs 6) raw ht (withHyp ho _) (withHyp h _)))))
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have ht := GuardPairProof.tagLiteral raw tag payload 2 (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact (orRight (orRight (orLeft (Classical.choice (ReverseTaggedProof.application n (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3) (xs 5) raw ht (withHyp hi _) (withHyp h _))))))
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have hc := bottomConstructorValue raw payload (GuardPairProof.pairLiteral raw tag payload 3 (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact (orRight (orRight (orRight (orLeft (Classical.choice (ReverseLeafProof.bottom n (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3) raw payload hc (withHyp h _)))))))
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have ht := GuardPairProof.tagLiteral raw tag payload 4 (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact (orRight (orRight (orRight (orRight (orLeft (Classical.choice (ReverseHeadTaggedProof.ordinary n (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3) (xs 5) raw ht (withHyp hi _) (withHyp h _))))))))
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have ht := GuardPairProof.tagLiteral raw tag payload 5 (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact (orRight (orRight (orRight (orRight (orRight (orLeft (Classical.choice (ReverseHeadTaggedProof.numbered n (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3) (xs 5) raw ht (withHyp hi _) (withHyp h _)))))))))
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have hf : Nonempty (Derivation body ((eqn tag (numeral 6) ⊓ eqn payload (numeral 0)) :: Delta) (eqn tag (numeral 6) ⊓ eqn payload (numeral 0))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact (orRight (orRight (orRight (orRight (orRight (orRight (orLeft (Classical.choice (GuardPairProof.nil raw tag payload (withHyp hp _) (andLeft hf) (andRight hf))))))))))
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have ht := GuardPairProof.tagLiteral raw tag payload 7 (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact (orRight (orRight (orRight (orRight (orRight (orRight (orRight (Classical.choice (ReverseTaggedProof.cons n (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3) (xs 5) raw ht (withHyp hi _) (withHyp h _))))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseObservedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseObservedProof
