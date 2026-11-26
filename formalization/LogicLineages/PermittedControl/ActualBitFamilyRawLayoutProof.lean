module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets
import LogicLineages.PermittedControl.OriginalMatrixLowDimensionCodeProof
import Mathlib.Data.List.Sort

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawLayout
open HeterogeneousSignedMatrixSlice (encodeRow)
open OriginalMatrixLowDimensionCode (exactRawSupport)
open OriginalMatrixLowDimension (supportSet)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualBitFamilyLowSlices (originalRows wantedBits coordinates dimension)

theorem exactRawFamilyLayout : ExactRawFamilyLayout := by
  intro family
  have rows (c : List BitRow) :
      (c.map encodeBitRow).map Prod.fst = (originalRows c).map encodeRow := by
    simp only [originalRows, List.map_map, Function.comp_def, encodeBitRow]
  have bits (c : List BitRow) :
      (c.map encodeBitRow).map Prod.snd = wantedBits c := by
    simp only [wantedBits, List.map_map, Function.comp_def, encodeBitRow]
  refine ⟨?_,?_,?_⟩
  · simp only [encodeFamily, List.map_map, Function.comp_def, rows]
  · simp only [encodeFamily, List.map_map, Function.comp_def, bits]
  · have flatten :
        (encodeFamily family).flatMap (List.map Prod.fst) =
          (family.flatMap originalRows).map encodeRow := by
        induction family with
        | nil => rfl
        | cons head tail ih =>
            change (head.map encodeBitRow).map Prod.fst ++
              (encodeFamily tail).flatMap (List.map Prod.fst) =
                (originalRows head ++ tail.flatMap originalRows).map encodeRow
            rw [List.map_append, rows, ih]
    unfold occurrences
    rw [flatten, exactRawSupport]

private theorem appears_true (ns : List Nat) (k : Nat) : appears ns k = true ↔ k ∈ ns := by
  induction ns with
  | nil => simp [appears]
  | cons head tail ih =>
      change (decide (head = k) || appears tail k) = true ↔ k ∈ head :: tail
      rw [Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
      exact or_congr eq_comm Iff.rfl

private theorem below_max (ns : List Nat) (k : Nat) (hk : k ∈ ns) : k ≤ ns.foldr max 0 := by
  induction ns with
  | nil => simp at hk
  | cons head tail ih =>
      rcases List.mem_cons.mp hk with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

private theorem namesFrom_eq (ns : List Nat) :
    namesFrom ns = (List.range ((ns.foldr max 0) + 1)).filter (appears ns) := by
  unfold namesFrom
  generalize List.range ((ns.foldr max 0) + 1) = candidates
  induction candidates with
  | nil => rfl
  | cons k ks ih =>
      cases h : appears ns k <;> simp [List.filterMap_cons, List.filter_cons, h, ih]

private theorem raw_names (raw : RawFamily) :
    (names raw).Pairwise (· < ·) ∧ (names raw).Nodup ∧
      ∀ k : Nat, k ∈ names raw ↔ k ∈ occurrences raw := by
  rw [names, namesFrom_eq]
  refine ⟨List.pairwise_lt_range.filter _, List.nodup_range.filter _,?_⟩
  intro k
  rw [List.mem_filter, List.mem_range, appears_true]
  exact ⟨And.right, fun hk => ⟨Nat.lt_succ_of_le (below_max _ _ hk),hk⟩⟩

theorem exactRawFamilyNames : ExactRawFamilyNames := by
  refine ⟨raw_names,?_⟩
  intro family
  have h := raw_names (encodeFamily family)
  have supportEq : (names (encodeFamily family)).toFinset = coordinates family := by
    ext k
    rw [List.mem_toFinset, h.2.2, (exactRawFamilyLayout family).2.2]
    simp [coordinates, supportSet]
  refine ⟨supportEq,?_⟩
  rw [← List.toFinset_card_of_nodup h.2.1, supportEq]

end LogicLineages.PermittedControl.ActualBitFamilyRawLayout
