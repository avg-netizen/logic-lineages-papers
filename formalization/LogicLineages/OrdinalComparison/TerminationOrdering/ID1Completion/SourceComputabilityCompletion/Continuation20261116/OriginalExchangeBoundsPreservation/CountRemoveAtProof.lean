module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountEffectZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (trans symm congSuc addZero addSucc)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open EraseInvariant Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCounts (list head tail needle rest query lc tc rc : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest z)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc list query)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tc tail query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest query))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn lc (OrdinaryArithmetic.addTerm rc (suc z)))) ⊓
       ((eqn needle query).not.imp (eqn lc rc)))) := by
  have hsame := CountEffectZeroProof.sameCounts tail needle rest query tc rc h ht hr
  have hyes : Nonempty (Derivation body ((eqn needle query) :: Delta)
      (eqn lc (OrdinaryArithmetic.addTerm rc (suc z)))) := by
    obtain ⟨he'⟩ := withHyp he (eqn needle query)
    have hq : Nonempty (Derivation body ((eqn needle query) :: Delta) (eqn head query)) :=
      ⟨trans he' (Derivation.hypothesis List.mem_cons_self)⟩
    have hv := ArgumentEntryCount.InternalProof.internalEqualCons body alpha _ list head tail query tc
      (withHyp hc _) (withHyp ht _) hq
    obtain ⟨hv⟩ := valueUnique ArgumentEntryCount.count lc (suc tc) ![list,query] (withHyp hl _) hv
    obtain ⟨hs⟩ := withHyp hsame (eqn needle query)
    have ha : Derivation body ((eqn needle query) :: Delta)
        (eqn (OrdinaryArithmetic.addTerm rc (suc z)) (suc rc)) :=
      trans (addSucc rc z) (congSuc (addZero rc))
    exact ⟨trans (trans hv (congSuc hs)) (symm ha)⟩
  have hno : Nonempty (Derivation body ((eqn needle query).not :: Delta) (eqn lc rc)) := by
    have hq : Nonempty (Derivation body ((eqn needle query).not :: Delta) (eqn head query).not) := by
      obtain ⟨he'⟩ := withHyp (withHyp he (eqn needle query).not) (eqn head query)
      have hn : Derivation body ((eqn head query) :: (eqn needle query).not :: Delta) (eqn needle query).not :=
        Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn
        (trans (symm he') (Derivation.hypothesis List.mem_cons_self)))⟩
    have hv := ArgumentEntryCount.InternalProof.internalUnequalCons body alpha _ list head tail query tc
      (withHyp hc _) (withHyp ht _) hq
    obtain ⟨hv⟩ := valueUnique ArgumentEntryCount.count lc tc ![list,query] (withHyp hl _) hv
    obtain ⟨hs⟩ := withHyp hsame (eqn needle query).not
    exact ⟨trans hv hs⟩
  obtain ⟨hy⟩ := hyes
  obtain ⟨hn⟩ := hno
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hy)
    (Derivation.implicationIntroduction hn)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveAtProof
