module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorEquivalenceProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG

theorem valid_computable : Computable valid :=
  RawValidator.check_primitive.to_comp.of_eq RawValidator.check_eq_valid

theorem reify_computable : Computable reifyCode := by
  apply (Computable.cond valid_computable Computable.option_some (Computable.const none)).of_eq
  intro c
  rw [reify_exact]
  cases valid c <;> rfl

theorem effective : RawSourceDAGTargets.Effective :=
  ⟨fun _ _ g => graph_length g,valid_computable,reify_computable⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG
