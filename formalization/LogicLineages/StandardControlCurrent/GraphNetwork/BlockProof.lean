module
public import LogicLineages.StandardControlCurrent.GraphNetwork.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSemanticStatementChecks
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork.BlockProof
open OrdinalComparison PolynomialGraphCompletion ExpressionSupportProof ExpressionNodeProof

 theorem full : Targets.BlockCoverage := by
  intro b ht hf hr ν
  have hresult : b.result ∉ allocated b.start b.term := by
    rw [mem_allocated]
    omega
  constructor
  · rintro ⟨σ,hframe,hrows⟩
    obtain ⟨hgraph,hlink⟩ :=
      (rows_hold_append _ _ σ).mp hrows
    have hlinkValue := (rows_hold_singleton _ σ).mp hlink
    have heq := (variable_equation _ _ σ).mp hlinkValue.2
    calc
      ν b.result = σ b.result := (hframe _ hresult).symm
      _ = σ (output b.start b.term) := heq
      _ = b.term.value σ := ExpressionSemanticStatementChecks.graph_soundness b.start b.term ht σ hgraph
      _ = b.term.value ν := source_value_congr _ _ _ (by
        intro i hi
        apply hframe
        rw [mem_allocated]
        have := hf i hi
        omega)
  · intro hvalue
    obtain ⟨σ,hframe,hgraph,hout⟩ :=
      ExpressionSemanticStatementChecks.total_graph_realization b.start b.term ht ν hf
    refine ⟨σ,hframe,?_⟩
    apply (rows_hold_append _ _ σ).mpr
    refine ⟨hgraph,(rows_hold_singleton _ σ).mpr ?_⟩
    refine ⟨variable_domain _ _ σ,?_⟩
    apply (variable_equation _ _ σ).mpr
    calc
      σ b.result = ν b.result := hframe _ hresult
      _ = b.term.value ν := hvalue
      _ = σ (output b.start b.term) := hout.symm
end LogicLineages.StandardControlCurrent.GraphNetwork.BlockProof
