module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph

theorem nodeCount_pos (t : Term) : 0 < nodeCount t := by cases t <;> simp [nodeCount]
theorem mem_allocated (start : Nat) (t : Term) (i : Nat) :
    i ∈ allocated start t ↔ start ≤ i ∧ i < start + nodeCount t :=
  SourceTermGraphSupportProof.mem_names start (nodeCount t) i

theorem output_mem_allocated (start : Nat) (t : Term) : output start t ∈ allocated start t := by
  rw [mem_allocated]
  have h := nodeCount_pos t
  unfold output
  omega

theorem exactAllocation : ExpandedGraphTargets.ExactAllocation := by
  intro start t
  refine ⟨nodeCount_pos t, SourceTermGraphSupportProof.names_nodup start (nodeCount t),
    mem_allocated start t, ?_⟩
  intro hf i hi hsource
  have hbound := (mem_allocated start t i).mp hi
  have hlow := hf i hsource
  omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
