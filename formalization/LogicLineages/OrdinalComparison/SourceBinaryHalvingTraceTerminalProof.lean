module
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Proof

theorem below_after (fuel : Nat) (s : TraceState) (h : s.1≤fuel+1) :
    (advance^[fuel] s).1<2 := by
  induction fuel generalizing s with
  | zero => change s.1<2; omega
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    by_cases hs : s.1<2
    · simp only [advance,hs,ite_true]; omega
    · simp only [advance,hs,ite_false]; omega

theorem bits_after (fuel : Nat) (s : TraceState) (h : ∀ b∈s.2,b<2) :
    ∀ b∈(advance^[fuel] s).2,b<2 := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    by_cases hs : s.1<2
    · simpa [advance,hs] using h
    · simp only [advance,hs,ite_false,List.mem_cons]
      intro b hb
      rcases hb with hb|hb
      · subst b; omega
      · exact h b hb

theorem zero_after (fuel : Nat) (s : TraceState) : (advance^[fuel] s).1=0 ↔ s.1=0 := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply,ih]
    by_cases hs : s.1<2
    · simp [advance,hs]
    · simp only [advance,hs,ite_false]; omega

theorem exactTerminalTrace : Targets.ExactTerminalTrace := by
  intro k
  exact ⟨below_after k (k,[]) (by omega),bits_after k (k,[]) (by simp),zero_after k (k,[])⟩
end LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Proof
