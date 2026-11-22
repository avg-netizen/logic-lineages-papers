module
public import LogicLineages.PermittedControl.ActualNormalizedTapeTargets
import LogicLineages.PermittedControl.ActualNormalizedTapeCertificateProof
import LogicLineages.PermittedControl.ActualNormalizedTapeClassProof
import LogicLineages.PermittedControl.ActualNormalizedTapeOutsideProof
import LogicLineages.PermittedControl.ActualRankedRowColumnsWeightsProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTape
open scoped Classical
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualZeroClassRecombinedRow ActualZeroClassOutsideAndShift
open SelectedNonlinearImageBounds (NonlinearField)

private theorem groupedAbsent (xs : List Read) (op : LowerOperand)
    (absent : op ∉ originalKeys xs) : groupedWeights xs op = 0 := by
  by_contra nonzero
  obtain ⟨rd,member,key⟩ := (exactGroupedWeights xs op).2.2 (Finsupp.mem_support_iff.mpr nonzero)
  exact absent (List.mem_map.mpr ⟨rd,member,key⟩)

private theorem removedWeights (selected : List LowerOperand) (xs : List Read) :
    groupedWeights (removeSelectedKeys selected xs) =
      (groupedWeights xs).filter (fun key => key ∉ selected) := by
  classical
  apply Finsupp.ext
  intro op
  rw [Finsupp.filter_apply]
  by_cases removed : op ∈ selected
  · rw [if_neg (not_not_intro removed)]
    apply groupedAbsent
    intro hmem
    obtain ⟨rd,member,hkey⟩ := List.mem_map.mp hmem
    have hkeep : rd.1.2 ∉ selected := by
      unfold removeSelectedKeys at member
      exact of_decide_eq_true (List.mem_filter.mp member).2
    exact hkeep (hkey.symm ▸ removed)
  · rw [if_pos removed]
    induction xs with
    | nil => rfl
    | cons rd tail ih =>
        by_cases inClass : rd.1.2 ∈ selected
        · have hne : rd.1.2 ≠ op := fun h => removed (h ▸ inClass)
          have hread : removeSelectedKeys selected (rd::tail) =
              removeSelectedKeys selected tail := by simp [removeSelectedKeys,inClass]
          rw [hread,ih]
          simp only [groupedWeights,Finsupp.add_apply,Finsupp.single_apply,if_neg hne,zero_add]
        · have hread : removeSelectedKeys selected (rd::tail) =
              rd :: removeSelectedKeys selected tail := by simp [removeSelectedKeys,inClass]
          rw [hread]
          simp only [groupedWeights,Finsupp.add_apply,ih]

theorem exactTapeOutsideRankedColumns : ExactTapeOutsideRankedColumns := by
  classical
  intro f ρ C r constant raw xs annotations bounded tape aligned actualC
  dsimp only
  let row := rankedRow r constant raw
  let selected := classReads f C xs annotations
  let chosen := finiteClassColumns r selected
  let outside := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations
  have rout : outside = removeSelectedKeys (originalKeys selected) xs :=
    exactTapeOutside f ρ C raw xs annotations tape aligned
  have woutside :
      groupedWeights outside =
        (groupedWeights raw).filter (fun op => op ∉ originalKeys selected) := by
    rw [rout,removedWeights,exactTapeWeights f ρ raw xs tape]
  have hclass := exactTapeRankedClass f ρ r constant raw xs annotations C bounded tape aligned actualC
  have valKeys (k : ValueKey r) : valueOperand r k ∈ originalKeys selected ↔ k ∈ chosen.1 := by
    exact List.mem_map.trans (hclass.2.2.2.1 k).symm
  have countKeys (k : CountKey r) : countOperand r k ∈ originalKeys selected ↔ k ∈ chosen.2 := by
    exact List.mem_map.trans (hclass.2.2.2.2.1 k).symm
  have rawCoeff := exactRankedCoefficients r constant raw
  have outCoeff := exactRankedCoefficients r 0 outside
  constructor
  · apply Finsupp.ext
    intro k
    change (rankedRow r 0 outside).value k = (row.value.filter (fun j => j ∉ chosen.1)) k
    by_cases nonlin : NonlinearField k.2
    · rw [outCoeff.2.2.1 k nonlin,woutside]
      simp only [Finsupp.filter_apply,valKeys,
        show row.value k = groupedWeights raw (valueOperand r k) from rawCoeff.2.2.1 k nonlin]
    · rw [outCoeff.2.2.2.1 k nonlin,Finsupp.filter_apply,
        show row.value k = 0 from rawCoeff.2.2.2.1 k nonlin]
      split <;> rfl
  · apply Finsupp.ext
    intro k
    change (rankedRow r 0 outside).count k = (row.count.filter (fun j => j ∉ chosen.2)) k
    rw [outCoeff.2.1 k,woutside]
    simp only [Finsupp.filter_apply,countKeys,
      show row.count k = groupedWeights raw (countOperand r k) from rawCoeff.2.1 k]

end LogicLineages.PermittedControl.ActualNormalizedTape
