module
public import LogicLineages.StandardControlCurrent.InactiveEliminationSemanticProof
public import LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveEliminationBlockProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm InactiveElimination

theorem matrix_step (xs : List Nat) (p : Formula) (i : Nat)
    (hi : i ∈ OrderedOccurrence.inactive xs p) (ν : Nat → Nat) :
    (∃ n : Nat, p.compile.eval (Function.update ν i n)) ↔ (eliminate i p).compile.eval ν := by
  simp only [NormalFormSemanticProof.actualBooleanCompilation]
  exact (InactiveEliminationSemanticProof.elimination xs p i hi ν).symm

theorem blockProgress : InactiveEliminationTargets.BlockProgress := by
  intro xs p i hn hi
  have hx := ((OrderedOccurrenceProof.exactInactive xs p i).mp hi).1
  refine ⟨hn.erase i,List.length_erase_add_one hx,?_,?_⟩
  · exact MixedRunnerBlockProof.block_erase xs i p.compile (eliminate i p).compile hn hx
      (matrix_step xs p i hi)
  · intro j hj hnot
    obtain ⟨hne,hm⟩ := InactiveEliminationSemanticProof.support p i j hj
    refine ⟨hm,?_⟩
    intro hmem
    exact hnot (hn.mem_erase_iff.mpr ⟨hne,hmem⟩)
end LogicLineages.StandardControlCurrent.InactiveEliminationBlockProof
