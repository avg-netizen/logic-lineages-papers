module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullForwardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
open CircuitLinear Narendran
open LogicLineages.ComputabilityKnowledge.CircuitReduction

/-- Full faithfulness of the frozen literal builder. Well-formedness is used
before the raw codec bridge, so dropped malformed references never enter the
semantic argument. The original input predicate retains its separate guard. -/
theorem full_circuit_encoding : CircuitLinear.Targets.FullCircuitEncoding := by
  intro c hc
  have hw := CircuitLinear.Proof.circuit_system_wellFormed c hc
  refine ⟨hw,?_⟩
  rw [CircuitLinear.Proof.raw_system_faithful (encodeCircuitSystem c) hw,
    scalar_run_semantics c hc]
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨p,_,hp⟩ := literal_rows_forward c hc v hv
    exact ⟨p,hp⟩
  · rintro ⟨p,hp⟩
    obtain ⟨v,hv,_⟩ := literal_rows_backward c hc p hp
    exact ⟨v,hv⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
