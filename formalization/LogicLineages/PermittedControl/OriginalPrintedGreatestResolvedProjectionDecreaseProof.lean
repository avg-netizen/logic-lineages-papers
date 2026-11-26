module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixRankProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
open OriginalPrintedGreatestResolvedMatrix (fullRows exactResolvedMatrixTopLinear)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalMatrixDenseRanks (renameRow renameTerm support)
open OriginalMatrixLowDimension (supportSet dimension)
open OriginalMatrixLinearLowerTable (lowerTable)
open ActualFiniteOrderBranches (rename exactPatternEnumeration exactBranchRealization)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames)
open MixedSameRankResidue (WeightedOperand)
open PreparedProjection (LowerOperand)
open HeterogeneousSignedMatrixSlice (Row)

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

theorem exactResolvedProjectionDecrease : ExactResolvedProjectionDecrease := by
  intro θ known gates p branch member ordered nonzero ops original
  let z := top branch
  let output := fullRows known gates p branch
  let source := matrix known gates p
  let tag := rename branch
  have names := (exactResolvedMatrixTopLinear θ known gates p branch member ordered).1
  have lifts (k : Nat) (h : k ∈ support (ranked known gates p branch)) : k ∈ support original := by
    change k ∈ support (output.map (renameRow tag)) at h
    change k ∈ support (source.map (renameRow tag))
    rw [supportRenamed] at h ⊢
    obtain ⟨name,occurs,rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨name,names name occurs,rfl⟩
  have exclude : argumentNames ops ⊆ (supportSet original).erase z := by
    intro k hk
    obtain ⟨op,h,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hmem : op ∈ lowerTable z (ranked known gates p branch) := h
    obtain ⟨below,orderedFilter⟩ := List.mem_filter.mp hmem
    have lt : op.rank < z := decide_eq_true_eq.mp orderedFilter
    obtain ⟨r,hr,term⟩ := List.mem_flatMap.mp below
    obtain ⟨t,ht,related⟩ := List.mem_map.mp term
    have tk : t.2.rank = k := (congrArg LowerOperand.rank related).trans eq
    have rk : k ∈ support original := lifts k
      (List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨t,ht,tk⟩⟩)
    exact Finset.mem_erase.mpr ⟨ne_of_lt (eq ▸ lt),List.mem_toFinset.mpr rk⟩
  have topOccurs : z ∈ supportSet original := by
    obtain ⟨_,keys,_,onto⟩ := (exactPatternEnumeration (support source) branch).mp member
    have inBound : z < branch.1 := by
      change branch.1 - 1 < branch.1
      omega
    obtain ⟨e,he,atTop⟩ := onto z inBound
    have fromSource : e.1 ∈ support source := by
      rw [← keys]
      exact List.mem_map.mpr ⟨e,he,rfl⟩
    have label := (exactBranchRealization θ (support source) branch member ordered).2.1 e he
    have hasTop : tag e.1 = z := label.1.trans atTop
    apply List.mem_toFinset.mpr
    change z ∈ support (source.map (renameRow tag))
    rw [supportRenamed]
    exact List.mem_map.mpr ⟨e.1,fromSource,hasTop⟩
  exact ⟨exclude,(Finset.card_le_card exclude).trans_lt (Finset.card_erase_lt_of_mem topOccurs)⟩

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
