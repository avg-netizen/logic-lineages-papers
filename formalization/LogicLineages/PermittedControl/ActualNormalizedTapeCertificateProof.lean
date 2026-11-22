module
public import LogicLineages.PermittedControl.ActualNormalizedTapeTargets
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualRankedRowColumnsWeightsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTape
open scoped Classical
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualZeroClassOutsideAndShift
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

theorem exactLegacyTape : ExactLegacyTape := by
  intro f ρ raw xs live success
  obtain ⟨out,found,keys,unique,reads,value,records⟩ :=
    (exactNormalizedReads f ρ raw).2 live
  have same : out = xs := Option.some.inj (found.symm.trans success)
  subst out
  refine ⟨live,reads,unique,?_,value,records⟩
  intro key
  change key ∈ xs.map (fun rd => rd.1.2) ↔ key ∈ (groupedWeights raw).support
  rw [keys]
  exact Finset.mem_toList

theorem exactTapeWeights : ExactTapeWeights := by
  intro f ρ raw xs tape
  classical
  apply Finsupp.ext
  intro op
  by_cases present : op ∈ (groupedWeights raw).support
  · obtain ⟨rd,member,eq⟩ := List.mem_map.mp ((tape.covers op).mpr present)
    exact (groupedUnique xs op rd tape.unique member eq).trans (by
      rw [← eq]
      exact (tape.records rd member).1)
  · have absent : op ∉ originalKeys xs := fun used => present ((tape.covers op).mp used)
    have zero : groupedWeights raw op = 0 := by
      by_contra h
      exact present (Finsupp.mem_support_iff.mpr h)
    rw [groupedAbsent xs op absent,zero]

theorem exactTapeRankedMembers : ExactTapeRankedMembers := by
  intro f ρ raw xs r c bounded tape rd retained
  let row := rankedRow r c raw
  obtain ⟨_,countWeight,valueWeight,_,countSupport,valueSupport⟩ :=
    exactRankedCoefficients r c raw
  obtain ⟨weight,nonzero,prior,priorMem,sameOp,_⟩ := tape.records rd retained
  have rankBound : rd.1.2.rank < r := by
    simpa only [sameOp] using bounded prior priorMem
  have inSupport : rd.1.2 ∈ (groupedWeights xs).support :=
    Finsupp.mem_support_iff.mpr (fun zero => nonzero (weight.trans zero))
  cases shape : rd.1.2 with
  | coordinate n => exact (by simp only [IsInRankedColumn,shape] : IsInRankedColumn row rd)
  | ordinary n F =>
      simp only [IsInRankedColumn,shape]
      intro active
      rw [shape] at rankBound
      let i : Fin r := ⟨n,rankBound⟩
      have literal : valueOperand r (i,F) = rd.1.2 := shape.symm
      have listed : valueOperand r (i,F) ∈ (groupedWeights xs).support := by
        rw [literal]
        exact inSupport
      refine ⟨i,rfl,(valueSupport (i,F)).mpr ⟨active,listed⟩,?_⟩
      rw [valueWeight (i,F) active,literal,← weight]
  | count n lam mu =>
      simp only [IsInRankedColumn,shape]
      rw [shape] at rankBound
      let i : Fin r := ⟨n,rankBound⟩
      have literal : countOperand r ((lam,mu),i) = rd.1.2 := shape.symm
      have listed : countOperand r ((lam,mu),i) ∈ (groupedWeights xs).support := by
        rw [literal]
        exact inSupport
      refine ⟨i,rfl,(countSupport ((lam,mu),i)).mpr listed,?_⟩
      rw [countWeight ((lam,mu),i),literal,← weight]


end LogicLineages.PermittedControl.ActualNormalizedTape
