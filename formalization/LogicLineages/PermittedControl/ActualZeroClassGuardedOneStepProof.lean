module
public import LogicLineages.PermittedControl.ActualZeroClassGuardedOneStepTargets
import LogicLineages.PermittedControl.ActualZeroClassConcreteChargeProof
import LogicLineages.PermittedControl.ActualZeroClassCommonTailProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsMaximumProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumRowProof
import LogicLineages.PermittedControl.SelectedLeadingSignCutoffActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassGuardedOneStep
open scoped Classical
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualZeroClassCommonTail ActualZeroClassConcreteCharge

theorem exactGuardedZeroClassOneStep : ExactGuardedZeroClassOneStep := by
  intro f B selected ρ strict r zRank constant raw xs paid bounded normalized
  dsimp only
  intro countReady active common
  obtain ⟨out, success, _, _, reads, sameSum, records⟩ :=
    (exactNormalizedReads f ρ raw).2 paid
  have identical : out = xs := Option.some.inj (success.symm.trans normalized)
  subst out
  have ceiling : ∀ t ∈ xs.map Prod.fst, ρ t.2.rank ≤ ρ zRank := by
    intro t member
    obtain ⟨rd, inXs, literal⟩ := List.mem_map.mp member
    subst t
    obtain ⟨prior, inRaw, sameOp, _⟩ := (records rd inXs).2.2
    apply strict.monotone
    rw [← sameOp]
    exact (bounded prior inRaw).2
  obtain ⟨annotations, C, aligned, maximum, member, maximal, dominates⟩ :=
    largestActualFull f B selected ρ zRank (xs.map Prod.fst) (xs.map Prod.snd)
      reads countReady ceiling active
  obtain ⟨ready, transfer⟩ := exactCommonTailGuards f B ρ C
    (xs.map Prod.fst) (xs.map Prod.snd) annotations aligned common
  refine ⟨annotations, C, aligned, maximum, member, maximal, dominates, ready, transfer, ?_⟩
  by_cases zero : (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 = 0
  · refine Or.inl ⟨zero, ?_⟩
    exact exactConcreteZeroClassCharge f B selected ρ strict C r constant raw xs annotations
      paid (fun rd original => (bounded rd original).1) normalized aligned ready member zero transfer
  · refine Or.inr ⟨zero, ?_⟩
    obtain ⟨decomposition, remainder⟩ :=
      exactSignedDecomposition f B selected ρ (ρ zRank) C constant (xs.map Prod.fst)
        (xs.map Prod.snd) annotations aligned ceiling member maximal dominates
    rw [sameSum]
    refine ⟨decomposition, remainder, ?_⟩
    intro tail
    let parts := rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations
    exact SelectedLeadingSignCutoff.actualLeadingSign f B selected (ρ zRank) C
      (slopeBound (xs.map Prod.fst)) (constant.natAbs + offsetBound (xs.map Prod.fst))
      parts.1 (constant + readSum xs) (constant + parts.2) tail dominates zero
      decomposition remainder

end LogicLineages.PermittedControl.ActualZeroClassGuardedOneStep
