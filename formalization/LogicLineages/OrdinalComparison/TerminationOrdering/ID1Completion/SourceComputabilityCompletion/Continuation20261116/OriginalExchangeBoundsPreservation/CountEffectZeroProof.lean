module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (trans addZero)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open EraseInvariant Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sameCounts (raw needle rest query lc rc : OTerm alpha)
    (h : Nonempty (Derivation body Delta (countEffect raw needle rest z)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc raw query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest query))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply formulaCases (eqn needle query)
  · obtain ⟨he⟩ := CountEffectBindingProof.equalQuery raw needle rest z query lc rc
      (withHyp h _) (withHyp hl _) (withHyp hr _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨trans he (addZero rc)⟩
  · exact CountEffectBindingProof.unequalQuery raw needle rest z query lc rc
      (withHyp h _) (withHyp hl _) (withHyp hr _) ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectZeroProof
