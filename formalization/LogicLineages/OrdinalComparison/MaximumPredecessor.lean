module
public import LogicLineages.OrdinalComparison.PredecessorTargets
public import LogicLineages.OrdinalComparison.FiniteCollapse
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# The exact finite-norm greatest predecessor

The implementation exhaustively enumerates the finite source norm ball.
It is an executable reference algorithm; no practical complexity bound is
claimed. Its specification quantifies over all actual normal predecessors,
not over an assumed adequate finite subdomain.
-/

namespace LogicLineages.OrdinalComparison

open Vendor.R1

def maximumPredecessor (a : NONote) (budget : Nat) : NONote :=
  if h : (predecessorSet a budget).Nonempty then
    (predecessorSet a budget).max' h
  else 0

theorem predecessorSet_nonempty (a : NONote) (budget : Nat) (ha : 0 < a) :
    (predecessorSet a budget).Nonempty := by
  refine ⟨0, (mem_predecessorSet _ _ _).mpr ⟨ha, ?_⟩⟩
  simp only [treeWeight]
  exact Nat.zero_le _

theorem maximumPredecessor_correct : Targets.MaximumPredecessorCorrect maximumPredecessor := by
  intro a budget ha
  have hs := predecessorSet_nonempty a budget ha
  simp only [maximumPredecessor, dif_pos hs]
  refine ⟨(mem_predecessorSet _ _ _).mp (Finset.max'_mem _ _), ?_⟩
  intro b hb
  exact Finset.le_max' _ b ((mem_predecessorSet _ _ _).mpr hb)

theorem maximumPredecessor_budget_mono (a : NONote) (ha : 0 < a) :
    Monotone (maximumPredecessor a) := by
  intro b c hbc
  have hm := (maximumPredecessor_correct a b ha).1
  exact (maximumPredecessor_correct a c ha).2 ⟨hm.1, hm.2.trans hbc⟩

theorem maximumPredecessor_finite : Targets.FiniteMaximumPredecessor maximumPredecessor := by
  intro n budget
  have ha : (0 : NONote) < NONote.ofNat (n + 1) :=
    ofNat_lt_ofNat (Nat.succ_pos n)
  have hm := maximumPredecessor_correct (NONote.ofNat (n + 1)) budget ha
  obtain ⟨k, hk, heq⟩ := below_ofNat hm.1.1
  have hkb : k ≤ budget := by simpa only [heq, norm_ofNat] using hm.1.2
  apply le_antisymm
  · rw [heq]
    change (ONote.ofNat k).repr ≤ (ONote.ofNat (min n budget)).repr
    simp only [ONote.repr_ofNat, Nat.cast_le]
    exact le_min (by omega) hkb
  · apply hm.2
    refine ⟨ofNat_lt_ofNat (Nat.lt_succ_of_le (min_le_left n budget)), ?_⟩
    simpa only [norm_ofNat] using min_le_right n budget

#print axioms maximumPredecessor_correct
#print axioms maximumPredecessor_finite

end LogicLineages.OrdinalComparison
