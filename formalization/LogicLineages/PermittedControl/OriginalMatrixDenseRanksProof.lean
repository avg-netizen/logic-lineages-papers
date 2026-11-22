module
public import LogicLineages.PermittedControl.OriginalMatrixDenseRanksTargets
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksTapeProof
import LogicLineages.PermittedControl.ActualCoordinateRankChartProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixDenseRanks
open MixedSameRankResidue (WeightedOperand actualSum orderedReads)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowSliceValue (valueAt)
open ActualCoordinateRankChart (rankOf rankValue size exactDenseRankChart)

private theorem orderedRename (f θ σ rename : Nat → Nat) (terms : List WeightedOperand)
    (ties : ∀ t ∈ terms, σ (rename t.2.rank) = θ t.2.rank) (values : List Nat) :
    orderedReads f σ (terms.map (renameTerm rename)) values ↔ orderedReads f θ terms values := by
  induction terms generalizing values with
  | nil =>
      cases values <;> rfl
  | cons t ts ih =>
      cases values with
      | nil => rfl
      | cons v vals =>
          obtain ⟨_,read,actual⟩ := exactRenamedOperand f θ σ rename t.2 (ties t List.mem_cons_self)
          have rest := ih (fun u hu => ties u (List.mem_cons_of_mem _ hu)) vals
          simp only [List.map_cons,orderedReads,renameTerm,read,actual,rest]

private theorem signedRename (rename : Nat → Nat) (terms : List WeightedOperand) (values : List Nat) :
    actualSum (terms.map (renameTerm rename)) values = actualSum terms values := by
  induction terms generalizing values with
  | nil => rfl
  | cons t ts ih =>
      cases values with
      | nil => rfl
      | cons v vs =>
          change t.1 * (v : Int) + actualSum (ts.map (renameTerm rename)) vs =
            t.1 * (v : Int) + actualSum ts vs
          rw [ih vs]

theorem exactRenamedMatrix : ExactRenamedMatrix := by
  intro f θ σ rename rows ties values
  induction rows generalizing values with
  | nil => cases values <;> rfl
  | cons r rows ih =>
      cases values with
      | nil => rfl
      | cons v vs =>
          have ht (t : WeightedOperand) (h : t ∈ r.2.2) :
              σ (rename t.2.rank) = θ t.2.rank :=
            ties _ (List.mem_flatMap.mpr ⟨r,List.mem_cons_self,List.mem_map.mpr ⟨t,h,rfl⟩⟩)
          have hr (name : Nat) (h : name ∈ support rows) : σ (rename name) = θ name := by
            obtain ⟨row,there,mem⟩ := List.mem_flatMap.mp h
            exact ties _ (List.mem_flatMap.mpr ⟨row,List.mem_cons_of_mem _ there,mem⟩)
          have hv : valueAt f σ r.2.1 (r.2.2.map (renameTerm rename)) v.1 ↔
              valueAt f θ r.2.1 r.2.2 v.1 := by
            unfold valueAt
            apply exists_congr
            intro vals
            rw [signedRename rename r.2.2 vals,orderedRename f θ σ rename r.2.2 ht vals]
          simp only [List.map_cons,actualRows,renameRow,hv,ih hr vs]

private theorem supportRenamed (rename : Nat → Nat) (rows : List Row) :
    support (rows.map (renameRow rename)) = (support rows).map rename := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      have head :
          ((r.2.2.map (renameTerm rename)).map (fun t => t.2.rank)) =
            ((r.2.2.map (fun t => t.2.rank)).map rename) := by
        simp only [List.map_map]
        apply congrArg (fun h : WeightedOperand → Nat => r.2.2.map h)
        funext t
        rcases t with ⟨w,operand⟩
        cases operand <;> rfl
      change ((r.2.2.map (renameTerm rename)).map (fun t => t.2.rank)) ++
          support (rows.map (renameRow rename)) =
        (((r.2.2.map (fun t => t.2.rank)) ++ support rows).map rename)
      rw [ih,List.map_append,head]

theorem exactDenseMatrix : ExactDenseMatrix := by
  intro f θ rows
  let names := support rows
  let rename := rankOf θ names
  have chart := exactDenseRankChart θ names
  have ns : support (denseRows θ rows) = names.map rename := supportRenamed rename rows
  refine ⟨chart.1,?_,ns,?_,?_⟩
  · simp only [denseRows,List.map_map,Function.comp_def,renameRow]
  · intro k h
    rw [ns] at h
    obtain ⟨name,mem,rfl⟩ := List.mem_map.mp h
    exact (chart.2.1 name mem).1
  · exact exactRenamedMatrix f θ (rankValue θ names) rename rows
      (fun n hn => (chart.2.1 n hn).2)

end LogicLineages.PermittedControl.OriginalMatrixDenseRanks
