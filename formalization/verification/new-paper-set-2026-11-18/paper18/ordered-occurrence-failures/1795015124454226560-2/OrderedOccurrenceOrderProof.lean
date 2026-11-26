module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRosterProof
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Permutation
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence

theorem strictOrder_of_pairwise (xs : List Nat) (ν : Nat → Nat)
    (hp : xs.Pairwise (fun i j => ν j < ν i)) : (strictOrder xs).eval ν := by
  rw [strictOrder,all_eval]
  intro q hq
  obtain ⟨⟨i,k⟩,hi,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  have hik := List.mk_mem_zipIdx_iff_getElem?.mp hi
  obtain ⟨hk,he⟩ := List.getElem?_eq_some_iff.mp hik
  obtain ⟨d,hd,hjd⟩ := List.mem_drop_iff_getElem.mp hj
  have ho := List.pairwise_iff_getElem.mp hp k (k+1+d) hk (by omega) (by omega)
  simpa only [Matrix.eval,Term.value,he,hjd] using ho

theorem orderedCoverage : OrderedOccurrenceTargets.OrderedCoverage := by
  intro xs hn ν
  classical
  by_cases he : ∃ i ∈ xs, ∃ j ∈ xs, i ≠ j ∧ ν i=ν j
  · exact Or.inl he
  · let ys := xs.mergeSort (fun i j => decide (ν j ≤ ν i))
    have hp : ys.Perm xs := List.mergeSort_perm xs _
    have hw : ys.Pairwise (fun i j => ν j ≤ ν i) := by
      have h := List.pairwise_mergeSort (le := fun i j => decide (ν j ≤ ν i))
        (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
        (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) xs
      simpa only [decide_eq_true_eq] using h
    have hy : ys.Nodup := hp.nodup_iff.mpr hn
    have hs : ys.Pairwise (fun i j => ν j < ν i) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have hle := List.pairwise_iff_getElem.mp hw i j hi hj hij
      have hne : ys[i] ≠ ys[j] := by
        intro h
        have := (List.getElem_inj_iff hy).mp h
        omega
      have hval : ν ys[i] ≠ ν ys[j] := by
        intro hv
        exact he ⟨ys[i],hp.mem_iff.mp (List.getElem_mem hi),ys[j],
          hp.mem_iff.mp (List.getElem_mem hj),hne,hv⟩
      omega
    exact Or.inr ⟨ys,List.mem_permutations.mpr hp,strictOrder_of_pairwise ys ν hs⟩
end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
