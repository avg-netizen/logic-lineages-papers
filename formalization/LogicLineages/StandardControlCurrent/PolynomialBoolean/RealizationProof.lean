module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.SemanticBasics

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.RealizationProof
open OrdinalComparison PolynomialGraphCompletion ExpressionSupportProof SemanticBasics

 theorem expr_realize (d start : Nat) (t : Expr) (hv : ValidExpr t)
    (hn : ∀ i ∈ t.variables, i < d) (hs : d ≤ start) (ρ : Nat → Nat) :
    ∃ ν : Nat → Nat,
      (∀ i, i < start ∨ start+nodeCount t ≤ i → ν i = ρ i) ∧
      GraphHolds start t ν ∧ ν (output start t) = t.value ρ := by
  obtain ⟨ν,hframe,hgraph,hout⟩ := ExpressionSemanticStatementChecks.total_graph_realization
    start t hv ρ (fun i hi => (hn i hi).trans_le hs)
  refine ⟨ν,?_,hgraph,hout⟩
  intro i hi
  apply hframe i
  rw [mem_allocated]
  omega

 theorem full : Targets.GlobalRealization := by
  intro d start p hv hs ρ
  induction p generalizing start ρ with
  | truth b =>
    refine ⟨ρ,fun _ _ => rfl,?_,?_⟩
    · intro r hr; simp [compile] at hr
    · cases b <;> simp [compile,Source.eval,WordLinearDecisionCompletion.Formula.eval]
  | atom rel a b =>
    obtain ⟨ν,hν,gν,oν⟩ := expr_realize d start a hv.1 hv.2.2.1 hs ρ
    obtain ⟨μ,hμ,gμ,oμ⟩ := expr_realize d (start+nodeCount a) b hv.2.1 hv.2.2.2
      (by omega) ν
    have hpres : ∀ i, i < start+nodeCount a → μ i = ν i := fun i hi => hμ i (Or.inl hi)
    have ga : GraphHolds start a μ :=
      (rows_hold_congr _ ν μ (fun r hr i hi =>
        (hpres i (expression_rows_below d start a hs hv.2.2.1 r hr i hi)).symm)).mp gν
    have oa : μ (output start a) = a.value ρ :=
      (hpres _ ((mem_allocated start a _).mp (output_mem_allocated start a)).2).trans oν
    have ob : μ (output (start+nodeCount a) b) = b.value ρ := by
      rw [oμ]
      exact source_value_congr b ν ρ (fun i hi => hν i (Or.inl ((hv.2.2.2 i hi).trans_le hs)))
    refine ⟨μ,?_,?_,?_⟩
    · intro i hi
      have hiμ : i < start+nodeCount a ∨ start+nodeCount a+nodeCount b ≤ i := by
        simp only [compile] at hi
        omega
      have hiν : i < start ∨ start+nodeCount a ≤ i := by
        simp only [compile] at hi
        omega
      exact (hμ i hiμ).trans (hν i hiν)
    · intro r hr
      rcases List.mem_append.mp hr with ha | hb
      · exact ga r ha
      · exact gμ r hb
    · simp only [compile,output_eval,oa,ob]
      cases rel <;> rfl
  | neg p ih =>
    obtain ⟨ν,hf,hg,ho⟩ := ih start hv hs ρ
    exact ⟨ν,hf,hg,not_congr ho⟩
  | conj p q ihp ihq =>
    obtain ⟨ν,hν,gν,oν⟩ := ihp start hv.1 hs ρ
    obtain ⟨μ,hμ,gμ,oμ⟩ := ihq (compile start p).1 hv.2 (hs.trans (end_ge start p)) ν
    have hpres : ∀ i, i < (compile start p).1 → μ i = ν i := fun i hi => hμ i (Or.inl hi)
    have gp := (graph_frame d start p hv.1 hs ν μ (fun i hi => (hpres i hi).symm)).mp gν
    have op := (output_frame start p μ ν hpres).trans oν
    have oq := oμ.trans (source_congr d q hv.2 ν ρ (fun i hi => hν i (Or.inl (hi.trans_le hs))))
    refine ⟨μ,?_,?_,and_congr op oq⟩
    · intro i hi
      have ep := end_ge start p
      have eq := end_ge (compile start p).1 q
      have hm : i < (compile start p).1 ∨ (compile (compile start p).1 q).1 ≤ i := by
        simp only [compile] at hi
        omega
      have hn : i < start ∨ (compile start p).1 ≤ i := by
        simp only [compile] at hi
        omega
      exact (hμ i hm).trans (hν i hn)
    · intro r hr
      rcases List.mem_append.mp hr with hp | hq
      · exact gp r hp
      · exact gμ r hq
  | disj p q ihp ihq =>
    obtain ⟨ν,hν,gν,oν⟩ := ihp start hv.1 hs ρ
    obtain ⟨μ,hμ,gμ,oμ⟩ := ihq (compile start p).1 hv.2 (hs.trans (end_ge start p)) ν
    have hpres : ∀ i, i < (compile start p).1 → μ i = ν i := fun i hi => hμ i (Or.inl hi)
    have gp := (graph_frame d start p hv.1 hs ν μ (fun i hi => (hpres i hi).symm)).mp gν
    have op := (output_frame start p μ ν hpres).trans oν
    have oq := oμ.trans (source_congr d q hv.2 ν ρ (fun i hi => hν i (Or.inl (hi.trans_le hs))))
    refine ⟨μ,?_,?_,or_congr op oq⟩
    · intro i hi
      have ep := end_ge start p
      have eq := end_ge (compile start p).1 q
      have hm : i < (compile start p).1 ∨ (compile (compile start p).1 q).1 ≤ i := by
        simp only [compile] at hi
        omega
      have hn : i < start ∨ (compile start p).1 ≤ i := by
        simp only [compile] at hi
        omega
      exact (hμ i hm).trans (hν i hn)
    · intro r hr
      rcases List.mem_append.mp hr with hp | hq
      · exact gp r hp
      · exact gμ r hq

end LogicLineages.StandardControlCurrent.PolynomialBoolean.RealizationProof
