module
public import LogicLineages.PermittedControl.ActualCanonicalNodeProgressTargets
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsMaximumProof
import LogicLineages.PermittedControl.ActualZeroClassCommonTailProof
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsProof
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataProof
import LogicLineages.PermittedControl.ActualFullValueLabelsProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceWitnessProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof
import LogicLineages.PermittedControl.ActualZeroClassValueConservationArithmeticProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalNodeProgress
open PreparedProjection MixedSameRankResidue
open ActualCanonicalNormalizedTape ActualCanonicalOperandGrouping
open ActualWeightedReadNormalization ActualCanonicalZeroTrace ActualReadChargeIteration
open ActualZeroClassReplacement ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open ActualFullValueLabels ActualFullValueMaximalMetadata ActualFiniteFullValueGuards
open ActualZeroClassCommonTail ActualZeroClassValueConservation

theorem exactCanonicalLocalProgress : ExactCanonicalLocalProgress := by
  intro f B selected ρ strict r top s live bounded available
  obtain ⟨xs,normal,tape⟩ := (exactCanonicalTapeDomain f ρ s.reads).mp live
  refine ⟨xs,normal,tape.outputReads,?_⟩
  by_cases active : ActiveAt top xs
  · refine Or.inr ⟨active,?_⟩
    obtain ⟨guards,ready,paid⟩ := available xs normal active
    let terms := xs.map Prod.fst
    let vals := xs.map Prod.snd
    let ls := labels terms
    have ceiling : ∀ t ∈ terms, ρ t.2.rank ≤ ρ top := by
      intro t member
      obtain ⟨rd,inXs,rfl⟩ := List.mem_map.mp member
      obtain ⟨prior,inRaw,sameOp,_⟩ := (tape.records rd inXs).2.2
      apply strict.monotone
      rw [← sameOp]
      exact (bounded prior inRaw).2
    obtain ⟨anns,C,aligned,maximum,member,_maximal,floor⟩ :=
      largestActualFull f B selected ρ top terms vals tape.outputReads guards.1 ceiling active
    have labelReads := exactFullValueLabels f B selected ρ terms vals anns aligned guards.1
    have nonempty : ls ≠ [] := by
      intro empty
      have length : ls.length = (fullValues f anns).length := labelReads.length_eq
      rw [empty] at length
      have noValues : fullValues f anns = [] := List.length_eq_zero_iff.mp length.symm
      rw [noValues] at member
      exact List.not_mem_nil member
    obtain ⟨a,listed,matching,ν,tied,passes⟩ :=
      (exactFiniteFullValueGuards f B selected ρ top ls ready).2 (ρ top) paid
    have actualMatch : Matches f ρ (pairs ls) a := by
      rw [Function.update_eq_self] at matching
      exact matching
    obtain ⟨D,maxValue,_,coeff,_⟩ := exactActualMaximalMetadata f B selected ρ terms vals anns
      aligned guards.1 nonempty a actualMatch
    have sameMax : D = C := Option.some.inj (maxValue.symm.trans maximum)
    subst D
    obtain ⟨routeReady,transfer⟩ := exactCommonTailGuards f B ρ C terms vals anns aligned guards.2
    refine ⟨a,anns,C,ν,listed,actualMatch,⟨tied,passes⟩,aligned,maximum,floor,
      guards,routeReady,transfer,coeff,?_⟩
    by_cases zero : maximalCoefficient terms a = 0
    · obtain ⟨old,legacy,_,_,_,_,_⟩ := (exactNormalizedReads f ρ s.reads).2 live
      obtain ⟨out,found,_,tapeEq,_,_⟩ := (exactCanonicalReads f ρ s.reads).2 old legacy
      have sameTape : out = xs := Option.some.inj (found.symm.trans normal)
      have frames : terms = groupTyped (s.reads.map Prod.fst) := by
        change xs.map Prod.fst = groupTyped (s.reads.map Prod.fst)
        exact (congrArg (fun ys : List Read => ys.map Prod.fst) sameTape).symm.trans tapeEq
      have rawZero : maximalCoefficient (groupTyped (s.reads.map Prod.fst)) a = 0 := by
        rw [← frames]
        exact zero
      have prepared : PreparedStep f B ρ r top s xs anns C a :=
        ⟨live,bounded,normal,active,guards,aligned,nonempty,actualMatch,maximum,floor,
          rawZero,routeReady,transfer⟩
      obtain ⟨out,witness⟩ := exactCanonicalZeroWitness f B selected ρ strict r top s xs anns C a prepared
      exact Or.inr ⟨zero,out,witness,(exactCanonicalZeroReplay f B selected ρ r top s out a witness).2.2.2.2.2⟩
    · left
      refine ⟨zero,?_⟩
      have identity := exactDoubledRowIdentity f ρ C terms vals anns aligned
      change 2 * readSum xs = (rowParts f C terms vals anns).1 * (C : Int) +
        2 * (rowParts f C terms vals anns).2 at identity
      change 2 * (s.constant + readSum s.reads) =
        maximalCoefficient terms a * (C : Int) + 2 * (s.constant + (rowParts f C terms vals anns).2)
      rw [tape.sameValue,coeff]
      omega
  · exact Or.inl active

end LogicLineages.PermittedControl.ActualCanonicalNodeProgress
