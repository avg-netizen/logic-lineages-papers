module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerForwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.SuccessorCoreProof
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
theorem atLayer (n : Nat) (xs : Fin 7 → OTerm alpha) (fuel node param out raw : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)))
    (hl : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n) out xs)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 5) (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3))))
    (ho : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 6) (suc (xs 4)) fuel (xs 0) (xs 1) (xs 2) (xs 3)))) :
    (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out raw)) ↔
     Nonempty (Derivation body Delta (Meaning.holds n raw (xs 4) (suc fuel) (xs 0) (xs 1) (xs 2) (xs 3)))) := by
  constructor
  · intro hm
    have hv := OriginalEnumerationValidity.Proof.internalEnumerationValidity n body alpha Delta node param out raw he hm
    exact LayerForwardProof.alternatives n xs fuel raw hv hi ho
      (OriginalEnumerationLayerFields.Proof.forward n xs out raw hl hm)
  · intro hm
    exact OriginalEnumerationLayerFields.Proof.backward n xs out raw hl
      (LayerReverseProof.alternatives n xs fuel raw hi ho hm)

theorem atLayerFormula (n : Nat) (xs : Fin 7 → OTerm alpha) (fuel node param out raw : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param)))
    (hl : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n) out xs)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 5) (xs 4) fuel (xs 0) (xs 1) (xs 2) (xs 3))))
    (ho : Nonempty (Derivation body Delta (Lists.Characterizes n (xs 6) (suc (xs 4)) fuel (xs 0) (xs 1) (xs 2) (xs 3)))) :
    Nonempty (Derivation body Delta
      ((graph2 contains (numeral 1) out raw).imp (Meaning.holds n raw (xs 4) (suc fuel) (xs 0) (xs 1) (xs 2) (xs 3)) ⊓
       (Meaning.holds n raw (xs 4) (suc fuel) (xs 0) (xs 1) (xs 2) (xs 3)).imp (graph2 contains (numeral 1) out raw))) := by
  apply andIntro
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    exact Classical.choice ((atLayer n xs fuel node param out raw
      (withHyp he _) (withHyp hl _) (withHyp hi _) (withHyp ho _)).mp ⟨Derivation.hypothesis List.mem_cons_self⟩)
  · apply Nonempty.intro
    apply Derivation.implicationIntroduction
    exact Classical.choice ((atLayer n xs fuel node param out raw
      (withHyp he _) (withHyp hl _) (withHyp hi _) (withHyp ho _)).mpr ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.SuccessorCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.SuccessorCoreProof
