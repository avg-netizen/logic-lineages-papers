module
public import LogicLineages.PermittedControl.ActualCanonicalZeroTraceTargets
import LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessorOrderedProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalZeroTrace
open ActualCanonicalSymbolicZeroSuccessor ActualCanonicalOperandGrouping
open ActualWeightedReadNormalization ActualReadChargeIteration
open ActualZeroClassReplacement ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow
open ActualShortCountCleanup ActualShortCountCleanupCharge ActualZeroClassOutputState
open ActualFullValueMaximalMetadata

theorem exactCanonicalZeroReplay : ExactCanonicalZeroReplay := by
  intro f B selected ρ r top s t a witness
  obtain ⟨xs,anns,C,moved,ledger,x₀,q,source,moves,_,_,_,_,_,clean,K,reads⟩ := witness
  let terms := xs.map Prod.fst
  let vals := xs.map Prod.snd
  let before := outsideCohort f C terms vals anns ++ moved
  let installed := s.constant + (replaceRow f C terms vals anns).2
  have resultEq : t = ⟨installed + shortShift before,retained before⟩ := by
    cases t
    exact congrArg₂ ReadState.mk K reads
  obtain ⟨old,legacy,_,_,_,_,_⟩ := (exactNormalizedReads f ρ s.reads).2 source.live
  obtain ⟨out,found,_,tapeEq,_,_⟩ := (exactCanonicalReads f ρ s.reads).2 old legacy
  have same : out = xs := Option.some.inj (found.symm.trans source.grouped)
  have frames : terms = groupTyped (s.reads.map Prod.fst) := same ▸ tapeEq
  have zero : maximalCoefficient terms a = 0 := by rw [frames]; exact source.zero
  have literal := exactOrderedSuccessorErasure f B selected ρ C s.constant xs anns a moved
    source.aligned source.guards.1 source.nonempty source.matched source.maximum zero moves
  obtain ⟨_,live,_,ranks,_,value,_,_,_,_,strict⟩ := clean
  rw [resultEq]
  refine ⟨?_,live,?_,ranks,value,strict⟩
  · change canonicalSuccessor s.constant (s.reads.map Prod.fst) a =
      some ⟨installed+shortShift before,(retained before).map Prod.fst⟩
    rw [canonicalSuccessor,← frames]
    exact literal
  · intro rd used
    obtain ⟨prior,origin,sameRank⟩ := ranks rd used
    exact sameRank.symm ▸ source.ranks prior origin

theorem exactCanonicalTraceReplay : ExactCanonicalTraceReplay := by
  intro f B selected ρ r top s t answers trace
  induction trace with
  | nil s =>
    exact ⟨rfl,id,id,(fun rd used => ⟨rd,used,rfl⟩),rfl,by simp⟩
  | @cons a answers s t u edge tail ih =>
    obtain ⟨step,outLive,outRank,edgeRanks,edgeValue,edgeCost⟩ :=
      exactCanonicalZeroReplay f B selected ρ r top s t a edge
    obtain ⟨rest,remainLive,remainRank,tailRanks,tailValue,tailCost⟩ := ih
    refine ⟨?_,fun _ => remainLive outLive,fun _ => remainRank outRank,?_,
      edgeValue.trans tailValue,?_⟩
    · change (canonicalSuccessor s.constant (eraseState s).terms a).bind (replay answers) =
        some (eraseState u)
      rw [step]
      exact rest
    · intro rd used
      obtain ⟨mid,inMid,midRank⟩ := tailRanks rd used
      obtain ⟨prior,inSource,sourceRank⟩ := edgeRanks mid inMid
      exact ⟨prior,inSource,midRank.trans sourceRank⟩
    · simp only [List.length_cons]
      omega

end LogicLineages.PermittedControl.ActualCanonicalZeroTrace
