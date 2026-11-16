module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseBranchAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseEffectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedErase
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm sucNeZeroApply)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem absent (total remainingWeight needleWeight : OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn total remainingWeight))) :
    Nonempty (Derivation body Delta (effect z total remainingWeight needleWeight)) := by
  apply andIntro
  · obtain ⟨d⟩ := withHyp h (eqn (z : OTerm alpha) z)
    exact ⟨Derivation.implicationIntroduction d⟩
  · have bad : Derivation body (eqn (z : OTerm alpha) (suc z) :: Delta) (eqn z (suc z)) :=
      Derivation.hypothesis List.mem_cons_self
    exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply (symm bad)))⟩

theorem found (total remainingWeight needleWeight : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 merge total needleWeight remainingWeight))) :
    Nonempty (Derivation body Delta (effect (suc z) total remainingWeight needleWeight)) := by
  apply andIntro
  · have bad : Derivation body (eqn (suc (z : OTerm alpha)) z :: Delta) (eqn (suc z) z) :=
      Derivation.hypothesis List.mem_cons_self
    exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply bad))⟩
  · obtain ⟨d⟩ := withHyp h (eqn (suc (z : OTerm alpha)) (suc z))
    exact ⟨Derivation.implicationIntroduction d⟩

theorem absentValue (total remainingWeight needleWeight : OTerm alpha)
    (h : Nonempty (Derivation body Delta (effect z total remainingWeight needleWeight))) :
    Nonempty (Derivation body Delta (eqn total remainingWeight)) := by
  obtain ⟨h⟩ := andLeft h
  exact ⟨Derivation.implicationElimination h (refl z)⟩

theorem foundValue (total remainingWeight needleWeight : OTerm alpha)
    (h : Nonempty (Derivation body Delta (effect (suc z) total remainingWeight needleWeight))) :
    Nonempty (Derivation body Delta (graph2 merge total needleWeight remainingWeight)) := by
  obtain ⟨h⟩ := andRight h
  exact ⟨Derivation.implicationElimination h (refl (suc z))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseEffectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseEffectProof
