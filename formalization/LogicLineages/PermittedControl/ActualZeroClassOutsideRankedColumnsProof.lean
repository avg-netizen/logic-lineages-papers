module
public import LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumnsTargets
import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftComplementProof
import LogicLineages.PermittedControl.ActualRankedZeroClassActualProof
import LogicLineages.PermittedControl.ActualRankedRowColumnsWeightsProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumns
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

private theorem groupedUnique (xs : List Read) (op : LowerOperand) (rd : Read)
    (unique : (originalKeys xs).Nodup) (member : rd ∈ xs) (key : rd.1.2 = op) :
    groupedWeights xs op = rd.1.1 := by
  classical
  induction xs with
  | nil => simp at member
  | cons first tail ih =>
      have unique' : (first.1.2 :: originalKeys tail).Nodup := unique
      obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp unique'
      rcases List.mem_cons.mp member with same | among
      · subst rd
        have absent : op ∉ originalKeys tail := by rw [← key]; exact fresh
        simp only [groupedWeights,Finsupp.add_apply,Finsupp.single_apply,if_pos key,
          groupedAbsent tail op absent,add_zero]
      · have notSame : first.1.2 ≠ op := by
          intro h
          exact fresh (List.mem_map.mpr ⟨rd,among,key.trans h.symm⟩)
        simp only [groupedWeights,Finsupp.add_apply,Finsupp.single_apply,if_neg notSame,zero_add,
          ih tailUnique among]

private theorem normalizationKeepsWeights (f : Nat → Nat) (ρ : Nat → Nat) (raw xs : List Read)
    (paid : liftedReads f ρ raw) (normalized : normalizeReads f ρ raw = some xs) :
    groupedWeights xs = groupedWeights raw := by
  classical
  obtain ⟨reported,hreported,keys,unique,_,_,weights⟩ := (exactNormalizedReads f ρ raw).2 paid
  have hsame : reported = xs := Option.some.inj (hreported.symm.trans normalized)
  subst reported
  apply Finsupp.ext
  intro op
  by_cases present : op ∈ (groupedWeights raw).support
  · have hkey : op ∈ originalKeys xs := by
      change op ∈ xs.map (fun rd => rd.1.2)
      rw [keys]
      exact Finset.mem_toList.mpr present
    obtain ⟨rd,member,eq⟩ := List.mem_map.mp hkey
    exact (groupedUnique xs op rd unique member eq).trans (by
      rw [← eq]
      exact (weights rd member).1)
  · have hkey : op ∉ originalKeys xs := by
      change op ∉ xs.map (fun rd => rd.1.2)
      rw [keys]
      exact fun h => present (Finset.mem_toList.mp h)
    have hzero : groupedWeights raw op = 0 := by
      by_contra hne
      exact present (Finsupp.mem_support_iff.mpr hne)
    rw [groupedAbsent xs op hkey,hzero]

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

theorem exactOutsideRankedColumns : ExactOutsideRankedColumns := by
  classical
  intro f ρ C r constant raw xs annotations paid bounded normalized aligned actualC
  dsimp only
  let row := rankedRow r constant raw
  let selected := classReads f C xs annotations
  let chosen := finiteClassColumns r selected
  let outside := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations
  have rout : outside = removeSelectedKeys (originalKeys selected) xs :=
    exactOutsideClass f ρ C raw xs annotations paid normalized aligned
  have woutside :
      groupedWeights outside =
        (groupedWeights raw).filter (fun op => op ∉ originalKeys selected) := by
    rw [rout,removedWeights,normalizationKeepsWeights f ρ raw xs paid normalized]
  have hclass := exactRankedClass f ρ r constant raw xs annotations C paid bounded normalized aligned actualC
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

end LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumns
