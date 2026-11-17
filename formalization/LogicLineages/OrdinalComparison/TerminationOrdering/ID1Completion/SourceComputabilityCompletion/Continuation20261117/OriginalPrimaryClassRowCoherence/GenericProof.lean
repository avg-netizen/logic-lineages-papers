module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.GenericProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem direction (T L : Program 2) (left right probe parameter out otherOut : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 L out left parameter)))
    (hr : Nonempty (Derivation body Delta (graph2 L otherOut right parameter)))
    (hi : Nonempty (Derivation body Delta (PrimaryMonotonicity.included out otherOut))) :
    Nonempty (Derivation body Delta
      ((graph3 (Membership.classTest T L (TransparentCandidate.candidate T)) (numeral 1) left probe parameter).imp
       (graph3 (Membership.classTest T L (TransparentCandidate.candidate T)) (numeral 1) right probe parameter))) := by
  let A := graph3 (Membership.classTest T L (TransparentCandidate.candidate T)) (numeral 1) left probe parameter
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := (CandidateIntegration.Proof.classFactor T L body alpha (A :: Delta)
    left probe parameter out (withHyp hl A)).mp ha
  have hm := PrimaryMonotonicity.InclusionProof.eliminate out otherOut probe
    (withHyp hi A) ⟨Derivation.conjunctionRight hf⟩
  obtain ⟨hm⟩ := hm
  have hfactor : Nonempty (Derivation body (A :: Delta)
      (graph2 T (numeral 1) probe parameter ⊓ graph2 Membership.contains (numeral 1) otherOut probe)) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hf) hm⟩
  obtain ⟨hrow⟩ := (CandidateIntegration.Proof.classFactor T L body alpha (A :: Delta)
    right probe parameter otherOut (withHyp hr A)).mpr hfactor
  exact ⟨Derivation.implicationIntroduction hrow⟩

theorem rows (T L : Program 2) (left right probe parameter out otherOut : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 L out left parameter)))
    (hr : Nonempty (Derivation body Delta (graph2 L otherOut right parameter)))
    (hi : Nonempty (Derivation body Delta
      (PrimaryMonotonicity.included otherOut out ⊓ PrimaryMonotonicity.included out otherOut))) :
    Nonempty (Derivation body Delta
      ((graph3 (Membership.classTest T L (TransparentCandidate.candidate T)) (numeral 1) left probe parameter).imp
       (graph3 (Membership.classTest T L (TransparentCandidate.candidate T)) (numeral 1) right probe parameter) ⊓
       (graph3 (Membership.classTest T L (TransparentCandidate.candidate T)) (numeral 1) right probe parameter).imp
       (graph3 (Membership.classTest T L (TransparentCandidate.candidate T)) (numeral 1) left probe parameter))) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hforward⟩ := direction T L left right probe parameter out otherOut hl hr ⟨Derivation.conjunctionRight hi⟩
  obtain ⟨hreverse⟩ := direction T L right left probe parameter otherOut out hr hl ⟨Derivation.conjunctionLeft hi⟩
  exact ⟨Derivation.conjunctionIntroduction hforward hreverse⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.GenericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.GenericProof
