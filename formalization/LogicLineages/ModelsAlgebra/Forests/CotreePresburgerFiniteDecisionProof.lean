module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecisionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecision.Proof
open FirstOrder Language

theorem encodedExact : Targets.EncodedExact := by
  intro Q n e p
  rw [satisfiableEncoded, CotreePresburgerCompiler.StatementChecks.satisfiabilityExact]
  simp only [Formula.realize_relabel]
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v ∘ e,hv⟩
  · rintro ⟨v,hv⟩
    refine ⟨v ∘ e.symm, ?_⟩
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hv

theorem orderedExact : Targets.OrderedExact := by
  intro Q _ _ p
  exact encodedExact Q _ _ p
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecision.Proof
