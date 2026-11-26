module
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets
import LogicLineages.PermittedControl.ActualLinearExitProof
import LogicLineages.PermittedControl.ActualShortCountCleanupChargeProof
import LogicLineages.PermittedControl.ActualZeroClassCommonTailProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsMaximumProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumRowProof
import LogicLineages.PermittedControl.SelectedLeadingSignCutoffActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualReadChargeIteration
open scoped Classical
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualZeroClassRecombinedRow ActualShortCountCleanup
open ActualZeroClassCommonTail ActualShortCountCleanupCharge

theorem exactReadProgress : ExactReadProgress := by
  intro f B selected ρ strict r zRank source paid bounded available
  obtain ⟨xs, normalized, _, _, reads, originalValue, records⟩ :=
    (exactNormalizedReads f ρ source.reads).2 paid
  by_cases active : ActiveAt zRank xs
  · obtain ⟨countReady,common⟩ := available xs normalized active
    have ceiling : ∀ t ∈ xs.map Prod.fst, ρ t.2.rank ≤ ρ zRank := by
      intro t member
      obtain ⟨rd, inXs, literal⟩ := List.mem_map.mp member
      subst t
      obtain ⟨prior, inRaw, sameOp, _⟩ := (records rd inXs).2.2
      apply strict.monotone
      rw [← sameOp]
      exact (bounded prior inRaw).2
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    obtain ⟨annotations,C,aligned,maximum,member,maximal,dominates⟩ :=
      largestActualFull f B selected ρ zRank terms values reads countReady ceiling active
    have chosen : ChosenClass f ρ zRank xs annotations C :=
      ⟨aligned,maximum,member,maximal,dominates⟩
    have guards : NodeGuards B ρ xs := ⟨countReady,common⟩
    obtain ⟨ready,transfer⟩ :=
      exactCommonTailGuards f B ρ C terms values annotations aligned common
    by_cases zero : (rowParts f C terms values annotations).1 = 0
    · obtain ⟨moved,ledger,x₀,q,movedAt,movedReads,anchor,origins,equations,_,_,_,_,_,
        replacement,_,_,_,cleaned⟩ :=
        exactConcreteLongOutputState f B selected ρ strict C r source.constant source.reads xs
          annotations paid (fun rd hm => (bounded rd hm).1) normalized aligned ready member
          zero transfer
      let before := outsideCohort f C terms values annotations ++ moved
      let installed := source.constant + (replaceRow f C terms values annotations).2
      let out : ReadState := ⟨installed + shortShift before,retained before⟩
      have witness := cleaned
      obtain ⟨_, live, _, ranks, _, value, _, _, _, _, charge⟩ := cleaned
      refine Or.inr ⟨out, ?_⟩
      refine ⟨?_,live,ranks,value,charge⟩
      exact ⟨xs,annotations,C,moved,ledger,x₀,q,normalized,active,guards,chosen,ready,transfer,
        zero,movedAt,movedReads,anchor,origins,equations,replacement,witness,rfl,rfl⟩
    · refine Or.inl ⟨xs,normalized,Or.inr ⟨active,annotations,C,chosen,zero,?_⟩⟩
      obtain ⟨equation,remainder⟩ := exactSignedDecomposition f B selected ρ (ρ zRank) C
        source.constant terms values annotations aligned ceiling member maximal dominates
      unfold stateValue
      rw [originalValue]
      refine ⟨equation,remainder,?_⟩
      intro tail
      let parts := rowParts f C terms values annotations
      exact SelectedLeadingSignCutoff.actualLeadingSign f B selected (ρ zRank) C
        (slopeBound terms) (source.constant.natAbs + offsetBound terms)
        parts.1 (source.constant + readSum xs) (source.constant + parts.2)
        tail dominates zero equation remainder
  · have noRead : ¬ ∃ rd ∈ xs, rd.1.1 ≠ 0 ∧ rd.1.2.rank = zRank ∧ NonlinearOperand rd.1.2 := by
      rintro ⟨rd,member,weight,top,nonlinear⟩
      exact active ⟨rd.1,List.mem_map.mpr ⟨rd,member,rfl⟩,weight,top,nonlinear⟩
    exact Or.inl ⟨xs,normalized,Or.inl ⟨active,
      ActualLinearExit.exactActualLinearExit f ρ zRank source.constant source.reads xs
        paid (fun rd hr => (bounded rd hr).2) normalized noRead⟩⟩

end LogicLineages.PermittedControl.ActualReadChargeIteration
