module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph

theorem fresh_mono {start stop : Nat} {t : Term} (h : start ≤ stop)
    (hf : Fresh start t) : Fresh stop t :=
  fun i hi => lt_of_lt_of_le (hf i hi) h

theorem not_allocated_below (start : Nat) (t : Term) (i : Nat)
    (hi : i < start) : i ∉ allocated start t := by
  intro hm
  have h := (mem_allocated start t i).mp hm
  omega

theorem graph_names_below (start : Nat) (t : Term) (stop : Nat)
    (hf : Fresh start t) (hs : start + nodeCount t ≤ stop) :
    ∀ i, i ∈ t.variables ∨ i ∈ allocated start t → i < stop := by
  intro i hi
  rcases hi with hsource | hnode
  · have h := hf i hsource
    omega
  · have h := (mem_allocated start t i).mp hnode
    omega

theorem graph_frame_after (start : Nat) (t : Term) (next : Nat) (u : Term)
    (ν σ : Nat → Nat) (ht : PlainBlockSplit.termHFree t = true)
    (hf : Fresh start t) (hn : start + nodeCount t ≤ next)
    (hframe : ∀ i, i ∉ allocated next u → σ i = ν i) :
    (graph start t).eval σ ↔ (graph start t).eval ν :=
  graph_eval_congr start t σ ν ht (fun i hi =>
    hframe i (not_allocated_below next u i (graph_names_below start t next hf hn i hi)))

theorem graph_update_after (start : Nat) (t : Term) (ν : Nat → Nat)
    (k value : Nat) (ht : PlainBlockSplit.termHFree t = true)
    (hf : Fresh start t) (hk : start + nodeCount t ≤ k) :
    (graph start t).eval (Function.update ν k value) ↔ (graph start t).eval ν := by
  apply graph_eval_congr start t _ ν ht
  intro i hi
  have hne : i ≠ k := Nat.ne_of_lt (graph_names_below start t k hf hk i hi)
  exact Function.update_of_ne hne _ _

theorem source_frame (t u : Term) (start : Nat) (ν σ : Nat → Nat)
    (hf : Fresh start t) (hframe : ∀ i, i ∉ allocated start u → σ i = ν i) :
    t.value σ = t.value ν :=
  term_value_congr t σ ν (fun i hi =>
    hframe i (not_allocated_below start u i (hf i hi)))

#print axioms fresh_mono
#print axioms not_allocated_below
#print axioms graph_names_below
#print axioms graph_frame_after
#print axioms graph_update_after
#print axioms source_frame
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
