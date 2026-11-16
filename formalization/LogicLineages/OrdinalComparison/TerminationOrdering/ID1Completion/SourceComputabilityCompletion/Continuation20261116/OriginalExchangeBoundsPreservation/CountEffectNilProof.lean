module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z eqn zRelabel)
open InternalTagArithmeticSupportProof (trans symm addZero)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open EraseInvariant Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unchanged (raw needle : OTerm alpha) :
    Nonempty (Derivation body Delta (countEffect raw needle raw z)) := by
  apply CountEffectIntroProof.introduce raw needle raw z
  intro beta j Theta query lc rc hj hl hr
  simp only [zRelabel] at hl hr ⊢
  obtain ⟨he⟩ := valueUnique ArgumentEntryCount.count lc rc ![raw.relabel j,query] hl hr
  have hsum : Nonempty (Derivation body Theta (eqn lc (OrdinaryArithmetic.addTerm rc z))) :=
    ⟨trans he (symm (addZero rc))⟩
  obtain ⟨hs⟩ := withHyp hsum (eqn (needle.relabel j) query)
  obtain ⟨he'⟩ := withHyp (show Nonempty (Derivation body Theta (eqn lc rc)) from ⟨he⟩)
    (eqn (needle.relabel j) query).not
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hs)
    (Derivation.implicationIntroduction he')⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectNilProof
