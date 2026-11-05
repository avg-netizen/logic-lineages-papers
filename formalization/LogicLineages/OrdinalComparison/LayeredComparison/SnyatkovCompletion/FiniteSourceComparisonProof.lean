module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparisonTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonStatementChecks

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparisonProof

theorem originalComparisonDecision : FiniteSourceComparisonTargets.OriginalComparisonDecision := by
  intro Γ hΓ τ a b ha hb mode
  obtain ⟨av, bv, hav, hbv, answer, hd, hsem⟩ :=
    LiteralFiniteSourceProof.actualSourceDecision Γ hΓ τ a b ha hb mode
  refine ⟨av, bv, hav, hbv, ?_⟩
  rw [GroundAdmissibleComparisonStatementChecks.universal_comparison Γ hΓ
    τ.level τ.level mode av bv]
  simpa only [FiniteSourceComparison.decide, hd, Option.getD_some] using hsem

theorem totalNumericDecision : FiniteSourceComparisonTargets.TotalNumericDecision :=
  Computable.option_getD SemanticFiniteVectorProgram.source_computable (Computable.const false)

theorem fullFiniteSourceComparison : FiniteSourceComparisonTargets.FullFiniteSourceComparison :=
  ⟨LiteralFiniteSourceProof.exactSourceTest, LiteralFiniteSourceProof.recursorFreePasses,
    LiteralFiniteSourceProof.acceptsSource_computable, totalNumericDecision,
    originalComparisonDecision⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparisonProof
