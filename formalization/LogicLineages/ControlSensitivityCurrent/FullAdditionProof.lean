module
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyAdditionProof
public import LogicLineages.ControlSensitivityCurrent.BinaryGeneratorProof
public import LogicLineages.OrdinalComparison.Control
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullAddition
open LogicLineages.OrdinalComparison
theorem completeAddition : Targets.CompleteAddition := by
  refine ⟨BinaryGenerator.exactTerminalTrace, BinaryGenerator.exactReconstruction,
    BinaryGenerator.uniformPrimitiveRecursive, ?_⟩
  intro f hf
  have hi : ∀ n : Nat, n < f n := fun n => (self_lt_Phi n).trans_le (hf.1 n)
  have hm : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact ((f n).lt_two_pow_self.trans (2 ^ f n).lt_two_pow_self).trans_le (hf.2 n)
  refine ⟨hm,hi,?_⟩
  intro p
  exact ⟨PolicyAddition.exactAddition p f hm (fun n => (hi n).le),
    PolicyAddition.exactOne p f hm (fun n => (hi n).le),
    PolicyAddition.exactBinaryDAG p f hm (fun n => (hi n).le)⟩
#audit_namespace LogicLineages.ControlSensitivityCurrent.FullAddition
end LogicLineages.ControlSensitivityCurrent.FullAddition
