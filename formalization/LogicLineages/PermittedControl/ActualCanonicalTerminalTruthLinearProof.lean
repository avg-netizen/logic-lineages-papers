module
public import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthTargets
import LogicLineages.PermittedControl.ActualLinearExitRowProof
import LogicLineages.PermittedControl.ActualLinearExitReplayProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection ActualMixedRowLeadingAnnotations
open ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualLinearExit ActualNormalizedTape

private theorem lowerMember (zRank : Nat) (xs : List Read) (rd : Read)
    (member : rd ∈ lowerReads zRank xs) : rd ∈ xs ∧ rd.1.2.rank < zRank := by
  simpa only [lowerReads,List.mem_filter,decide_eq_true_eq] using member

theorem exactCertifiedLinearExit : ExactCertifiedLinearExit := by
  intro f ρ zRank constant raw xs bound tape noActive
  dsimp only
  have reads := tape.outputReads
  have sameSum := tape.sameValue
  have records := tape.records
  let rs := lowerReads zRank xs
  let ops := table zRank xs
  let row := exitRow zRank constant xs
  have greatest (rd : Read) (member : rd ∈ xs) : rd.1.2.rank ≤ zRank := by
    obtain ⟨prior, old, key, _⟩ := (records rd member).2.2
    rw [← key]
    exact bound prior old
  have linear (rd : Read) (member : rd ∈ xs) (top : rd.1.2.rank = zRank) :
      LinearOperand rd.1.2 :=
    linearOfNotNonlinear rd.1.2 (fun hn => noActive ⟨rd,member,(records rd member).2.1,top,hn⟩)
  have hits := (exactInputChecks f ρ xs).mpr reads
  simp only [checkedReads,List.all_eq_true,decide_eq_true_eq] at hits
  have indexBound (j : Nat) (hj : j < ops.length) : j < rs.length := by
    simpa only [ops,table,List.length_map,rs] using hj
  have item (j : Nat) (hj : j < ops.length) : ops[j] = (rs[j]'(indexBound j hj)).1.2 := by
    simp only [ops,table,List.getElem_map,rs]
  have original (j : Nat) (hj : j < rs.length) :
      lowerOperandRead f ρ rs[j].1.2 = some (some rs[j].2) :=
    hits _ (lowerMember zRank xs _ (List.getElem_mem hj)).1
  have prepared : PreparedInput ops (.atom (.nonnegative row)) := exitPrepared zRank constant xs
  refine ⟨prepared, ?_, ?_⟩
  · let ν (i : Nat) := (rs.map Prod.snd).getD (i-1) 0
    have slot : OriginalSlots ν rs := by
      intro j hj
      simp [ν,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj]
    refine ⟨ν,slot,?_⟩
    intro j hj
    change ops[j].rank < zRank ∧ LowerOperandActual f ρ ops[j] (ν (j+1))
    rw [item j hj,slot j (indexBound j hj)]
    exact ⟨(lowerMember zRank xs _ (List.getElem_mem (indexBound j hj))).2,
      (preparedTiedProjection.1 _ _ _ _).mp (original j (indexBound j hj))⟩
  · intro ν tie
    have atSlot (j : Nat) (hj : j < ops.length) :
        lowerOperandRead f ρ ops[j] = some (some (ν (j+1))) :=
      (preparedTiedProjection.1 _ _ _ _).mpr (tie j hj).2
    have values : OriginalSlots ν rs := by
      intro j hj
      have hj' : j < ops.length := by simpa only [ops,table,List.length_map,rs] using hj
      have found := atSlot j hj'
      rw [item j hj'] at found
      exact Option.some.inj (Option.some.inj (found.symm.trans (original j hj)))
    have forAny (z : Nat) :
        NormalForm.rowValue row (Function.update ν 0 z) =
          constant + readSum (replay zRank z xs) :=
      rowReplay ν zRank z constant xs greatest values
    refine ⟨values, atSlot, ?_, ?_⟩
    · intro z
      exact ⟨(preparedTiedProjection.2 f zRank ρ ops (.atom (.nonnegative row)) ν prepared tie).1 z,
        replayPaid f ρ zRank z xs reads linear, forAny z⟩
    · rw [forAny, replaySelf f ρ zRank xs reads linear, ← sameSum]

end LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
