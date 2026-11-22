module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupportTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionPreparedProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.PreparedParameterOutputProof
import LogicLineages.PermittedControl.PreparedParameterCodeProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupport
open OriginalPrintedPlainMatrixLinearProjection (table top formula exactAlreadyLinearPreparedCircuit)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open OriginalMatrixDenseRanks (renameRow renameTerm renameOperand support)
open OriginalMatrixLowDimension (supportSet dimension)
open OriginalMatrixLinearLowerTable (lowerTable lowerReadStable)
open ActualFiniteOrderBranches (rename realized exactPatternEnumeration exactBranchRealization)
open PreparedProjection (LowerOperand LowerOperandActual lowerOperandRead
  eliminatePreparedFormula preparedProjectionSyntax preparedProjectionCodeExact preparedTiedProjection)
open HeterogeneousSignedMatrixSlice (Row)
open MixedSameRankResidue (WeightedOperand)

private theorem literalOrigin (z : Nat) (ranked : List Row) (op : LowerOperand)
    (inTape : op ∈ lowerTable z ranked) :
    ∃ row ∈ ranked, ∃ t ∈ row.2.2, t.2 = op ∧ op.rank < z := by
  obtain ⟨below,ordered⟩ := List.mem_filter.mp inTape
  obtain ⟨r,hr,inRow⟩ := List.mem_flatMap.mp below
  obtain ⟨t,ht,eq⟩ := List.mem_map.mp inRow
  exact ⟨r,hr,t,ht,eq,decide_eq_true_eq.mp ordered⟩

private theorem rankRenamed (r : Nat → Nat) (t : WeightedOperand) :
    (renameTerm r t).2.rank = r t.2.rank := by
  rcases t with ⟨weight,op⟩
  cases op <;> rfl

theorem exactProjectedLowerSupport : ExactProjectedLowerSupport := by
  intro f θ known gates p plain branch member guard nonzero linear minimum positive
  let original := matrix known gates p
  let ranked := renamed known gates p branch
  let ops := table known gates p branch
  let z := top branch
  let q := formula known gates p branch minimum positive
  have prep := (exactAlreadyLinearPreparedCircuit f θ known gates p plain branch member guard linear minimum positive).1
  have outFacts := preparedProjectionSyntax ops q prep
  have origin (op : LowerOperand) (mem : op ∈ ops) :
      ∃ row ∈ ranked, ∃ t ∈ row.2.2, t.2 = op ∧ op.rank < z :=
    literalOrigin z ranked op mem
  have exclude : argumentNames ops ⊆ (supportSet ranked).erase z := by
    intro k hk
    obtain ⟨op,h,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    obtain ⟨r,hr,t,ht,related,lt⟩ := origin op h
    have tk : t.2.rank = k := (congrArg LowerOperand.rank related).trans eq
    exact Finset.mem_erase.mpr ⟨ne_of_lt (eq ▸ lt),
      List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨t,ht,tk⟩⟩)⟩
  have topOccurs : z ∈ supportSet ranked := by
    obtain ⟨_,keys,_,onto⟩ := (exactPatternEnumeration (support original) branch).mp member
    have inBound : z < branch.1 := by
      change branch.1 - 1 < branch.1
      omega
    obtain ⟨e,he,atTop⟩ := onto z inBound
    have fromSource : e.1 ∈ support original := by
      rw [← keys]
      exact List.mem_map.mpr ⟨e,he,rfl⟩
    obtain ⟨r,hr,inRow⟩ := List.mem_flatMap.mp fromSource
    obtain ⟨t,ht,name⟩ := List.mem_map.mp inRow
    have label := (exactBranchRealization θ (support original) branch member guard).2.1 e he
    have rankedTerm : (renameTerm (rename branch) t).2.rank = z :=
      (rankRenamed (rename branch) t).trans ((congrArg (rename branch) name).trans (label.1.trans atTop))
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
      ⟨renameRow (rename branch) r,List.mem_map.mpr ⟨r,hr,rfl⟩,
        List.mem_map.mpr ⟨renameTerm (rename branch) t,List.mem_map.mpr ⟨t,ht,rfl⟩,rankedTerm⟩⟩)
  have actualSlot (n : Nat) (hn : n ∈ (eliminatePreparedFormula q).variables) :
      ∃ j : Nat, ∃ hj : j < ops.length, n = j+1 ∧ (ops[j]).rank < z := by
    obtain ⟨pos,bound⟩ := outFacts.2.2.2 n hn
    let j := n-1
    have hj : j < ops.length := by
      dsimp only [j]
      omega
    have eq : n = j+1 := by dsimp only [j]; omega
    obtain ⟨r,hr,t,ht,originalField,lower⟩ := origin ops[j] (List.getElem_mem hj)
    exact ⟨j,hj,eq,lower⟩
  have smaller := (Finset.card_le_card exclude).trans_lt (Finset.card_erase_lt_of_mem topOccurs)
  refine ⟨outFacts.2.1,outFacts.2.2.1,actualSlot,origin,exclude,smaller,
    preparedProjectionCodeExact.2.2.2 ops q,?_⟩
  intro ν fit n hn
  obtain ⟨j,hj,eq,low⟩ := actualSlot n hn
  have actual := (fit j hj).2
  change LowerOperandActual f (realized θ branch) ops[j] (ν (j+1)) at actual
  rw [← eq] at actual
  have hit := (preparedTiedProjection.1 f (realized θ branch) ops[j] (ν n)).mpr actual
  exact ⟨j,hj,eq,hit,fun v => (lowerReadStable f (realized θ branch) z v ops[j] low).trans hit⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupport
