module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionTransportProof
public import Mathlib.Computability.Halting
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof

theorem blankHaltingUndecidable : Targets.BlankHaltingUndecidable := by
  classical
  intro h
  obtain ⟨U,hU,he⟩ := effectiveBlankReduction
  have hf : Computable (fun c : Nat.Partrec.Code => translate U (Encodable.encode c)) :=
    (hU.comp Primrec.encode).to_comp
  apply ComputablePred.halting_problem 0
  have ht : ComputablePred (fun c : Nat.Partrec.Code =>
      SourceBlankMachineSimulation.Halts (translate U (Encodable.encode c))) :=
    (h.decide.comp hf).computablePred
  exact ht.of_eq he
end LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Proof
