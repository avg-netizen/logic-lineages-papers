module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxFiniteProof
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Proof

theorem tableSize_primitive : Primrec tableSize :=
  Primrec.list_foldr Primrec.id (Primrec.const (0 : Nat))
    (Primrec.nat_max.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem lookup_primitive : Primrec (fun p : List Nat × List Nat × Nat =>
    singleCoreBoxLookup p.1 p.2.1 p.2.2) := by
  have hFind : Primrec (fun p : List Nat × List Nat × Nat =>
      p.1.findIdx (fun j => decide (j = p.2.2))) :=
    Primrec.list_findIdx Primrec.fst
      (Primrec.eq.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).decide
  exact (Primrec.list_getD 1).comp (Primrec.fst.comp Primrec.snd) hFind

theorem finiteTable_computable : Computable₂ finiteTable := by
  have hsupport : Primrec (fun p : (List Nat × List Nat) × Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hword : Primrec (fun p : (List Nat × List Nat) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact (Primrec.list_map
    (Primrec.list_range.comp (tableSize_primitive.comp Primrec.fst))
    (lookup_primitive.comp (hsupport.pair (hword.pair Primrec.snd))).to₂).to_comp

theorem member_lt_tableSize (support : List Nat) {i : Nat} (hi : i ∈ support) :
    i < tableSize support := by
  induction support with
  | nil => cases hi
  | cons j rest ih =>
    simp only [tableSize, List.foldr_cons]
    rcases List.mem_cons.mp hi with rfl | hi
    · exact lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_left _ _)
    · exact lt_of_lt_of_le (ih hi) (Nat.le_max_right _ _)

theorem finiteTable_length (support word : List Nat) :
    (finiteTable support word).length = tableSize support := by
  simp only [finiteTable, List.length_map, List.length_range]

theorem finiteTable_valuation (support word : List Nat)
    (hlen : word.length = support.length) (i : Nat) :
    BaseTermPrograms.valuation (finiteTable support word) i =
      singleCoreBoxLookup support word i := by
  unfold BaseTermPrograms.valuation
  by_cases hi : i < tableSize support
  · rw [List.getD_eq_getElem _ 1 (by simpa only [finiteTable_length] using hi)]
    simp only [finiteTable, List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simpa only [finiteTable_length] using Nat.le_of_not_gt hi)]
    symm
    exact BalancedSmallBox.Proof.lookup_outside support word hlen i
      (fun hm => hi (member_lt_tableSize support hm))

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Proof
