module
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowAlgebraProof
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadCollectedRow.Proof
open CommonHeadLargeRow

private theorem value_collection (lam : Ordinal) (K : Int) (row : Row) :
    value lam K (collect row)=value lam K row := by
  have h := exactWeightedCollection row (fun t=>(actualHeadValue lam t : Int))
  change ((collect row).map (fun a=>a.1*(actualHeadValue lam a.2 : Int))).sum =
    (row.map (fun a=>a.1*(actualHeadValue lam a.2 : Int))).sum at h
  exact congrArg (fun z=>K+z) h

private theorem attained_maximum (row : Row) (hne : row≠[]) :
    ∃ a∈row, ∀ b∈row, b.2≤a.2 := by
  induction row with
  | nil => exact (hne rfl).elim
  | cons c rest ih =>
    by_cases hr : rest=[]
    · subst rest
      exact ⟨c,by simp,by simp⟩
    · obtain ⟨a,ha,hmax⟩ := ih hr
      rcases le_total c.2 a.2 with hca | hac
      · refine ⟨a,List.mem_cons_of_mem c ha,?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hca
        · exact hmax b hb
      · refine ⟨c,by simp,?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact le_rfl
        · exact (hmax b hb).trans hac

theorem actualCollectedDominance : Targets.ActualCollectedDominance := by
  intro lam hl hs K row hdomain
  have hc := literalCollectedSupport row
  have hthreshold : threshold K (collect row)≤threshold K row := by
    exact max_le_max le_rfl (max_le_max (Nat.mul_le_mul_left 2 hc.2.2) le_rfl)
  have hcolDomain : ∀ a∈collect row,
      actualOrdinalNorm lam≤a.2 ∧ threshold K (collect row)≤a.2 := by
    intro a ha
    obtain ⟨b,hb,hba⟩ := (hc.2.1 a ha).2.2
    have hd := hdomain b hb
    rw [hba] at hd
    exact ⟨hd.1,hthreshold.trans hd.2⟩
  have hsign : ∀ a∈collect row, (∀ b∈collect row,b.2≤a.2) →
      Int.sign (value lam K row)=Int.sign a.1 := by
    intro a ha hmax
    rw [← value_collection lam K row]
    exact CommonHeadLargeRow.Proof.actualHeadDominance lam hl hs K (collect row)
      hc.1 hcolDomain a ha (hc.2.1 a ha).1 hmax
  refine ⟨?_,?_,hsign⟩
  · intro hempty
    rw [← value_collection lam K row,hempty]
    simp only [value,List.map_nil,List.sum_nil,add_zero]
  · intro hne
    obtain ⟨a,ha,hmax⟩ := attained_maximum (collect row) hne
    exact ⟨a,ha,hmax,hsign a ha hmax⟩
end LogicLineages.OrdinalComparison.CommonHeadCollectedRow.Proof
