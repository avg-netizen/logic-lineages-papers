module
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionOneProof
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionDAGProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof

theorem fullSourceAddition : Targets.FullSourceAddition :=
  ⟨fun _ => add_witness, fun _ => add_formula, one_formula, dag_correct⟩
end LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
