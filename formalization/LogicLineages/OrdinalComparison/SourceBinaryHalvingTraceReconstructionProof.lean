module
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceTerminalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Proof
open SourceAdditionCompletion

theorem advance_reconstruct (s : TraceState) :
    (advance s).2.foldl wrap (binaryDAG (advance s).1)=s.2.foldl wrap (binaryDAG s.1) := by
  by_cases hs : s.1<2
  · simp [advance,hs]
  · have hb : binaryDAG s.1=wrap (binaryDAG (s.1/2)) (s.1%2) := by
      rw [binaryDAG]
      simp [hs,wrap]
    simp only [advance,hs,ite_false,List.foldl_cons]
    rw [←hb]

theorem iterate_reconstruct (fuel : Nat) (s : TraceState) :
    (advance^[fuel] s).2.foldl wrap (binaryDAG (advance^[fuel] s).1)=s.2.foldl wrap (binaryDAG s.1) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (advance s)).trans (advance_reconstruct s)

theorem exactReconstruction : Targets.ExactReconstruction := by
  intro k
  have h := iterate_reconstruct k (k,[])
  have ht := (exactTerminalTrace k).1
  have hb : binaryDAG (trace k).1=(if (trace k).1=0 then BinaryDAG.zero else BinaryDAG.one) := by
    rw [binaryDAG]
    simp only [ht,dif_pos]
  change (trace k).2.foldl wrap (binaryDAG (trace k).1)=binaryDAG k at h
  rw [hb] at h
  exact h
end LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Proof
