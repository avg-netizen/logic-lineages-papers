module
public import LogicLineages.PermittedControl.StageEmitterHighTargets
import LogicLineages.PermittedControl.StageEmitterEmissionProof
import LogicLineages.PermittedControl.StageEmitterEffectivityProof
import LogicLineages.PermittedControl.StageCallbackLevelOrderProof
import LogicLineages.PermittedControl.ClosedBlockDecisionReductionProof

public section
namespace LogicLineages.PermittedControl.StageEmitter
open StageCallbackLevelOrder (levelOrder exactLevelOrderSupplierShape exactLevelOrderSupplierExact)
open ClosedBlockDecision (exactClosedBlockReduction)

theorem exactConditionalEmitter : ExactConditionalEmitter := by
  intro R hR hE f B selected
  exact ⟨levelOrder,exactLevelOrderSupplierShape,exactLevelOrderSupplierExact f B selected,
    highCode R,(exactHighCodeEffectivity R hE).2,exactStageEmission R hR B⟩

theorem exactConditionalClosedBlockDecision : ExactConditionalClosedBlockDecision := by
  rintro ⟨R,hR,hE⟩
  exact exactClosedBlockReduction
    (exactConditionalEmitter R hR hE _ _ (Or.inl ⟨rfl,rfl⟩))
    (fun b => exactConditionalEmitter R hR hE _ _ (Or.inr ⟨b,rfl,rfl⟩))

theorem fullStageEmitterHigh : FullStageEmitterHigh :=
  ⟨exactStageEmission,exactHighCodeEffectivity,exactConditionalEmitter,exactConditionalClosedBlockDecision⟩

#print axioms exactStageEmission
#print axioms exactHighCodeEffectivity
#print axioms exactConditionalEmitter
#print axioms exactConditionalClosedBlockDecision
#print axioms fullStageEmitterHigh
end LogicLineages.PermittedControl.StageEmitter
