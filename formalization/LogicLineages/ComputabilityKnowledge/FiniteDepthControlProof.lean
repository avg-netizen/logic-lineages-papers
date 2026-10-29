module

public import LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthControl
public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeProof
public import LogicLineages.OrdinalComparison.Control

@[expose] public section

/-! External Codex continuation: composition with the already checked literal
numerical hierarchy. No redefinition of F and no ordinal admissibility claim. -/
namespace LogicLineages.ComputabilityKnowledge.FiniteDepthControlProof
open PositiveExpression CircuitReduction FiniteDepthEnvelope

theorem finiteDepthControl : Comparators.FiniteDepthControl.Target := by
  intro e he
  obtain ⟨_,_,_,_,_,hg,_⟩ := FiniteDepthEnvelopeProof.literalAffineConstruction e
  refine ⟨hg,fun d => FiniteDepthEnvelopeProof.sameVariables d e,?_⟩
  intro ρ
  have hp : 0 < (envelope e).eval ρ := PositiveExpressionProperties.eval_positive ρ _
  refine ⟨hp,?_⟩
  exact (FiniteDepthEnvelopeProof.depthTwoBound e he ρ).trans
    (LogicLineages.OrdinalComparison.two_tower_le_fastControl (by decide) hp)

end LogicLineages.ComputabilityKnowledge.FiniteDepthControlProof
