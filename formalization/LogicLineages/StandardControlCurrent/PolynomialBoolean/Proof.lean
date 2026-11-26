module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.DecisionProof
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.ProgramsProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineLeastProgramsProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.Proof
open OrdinalComparison
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair Code.package
  ClosedWordDecisionCompletion.Machine.solve

theorem compilerPrograms : Targets.CompilerPrograms := by
  have hp := ProgramsProof.package_primitive.to_comp
  have hd := Computable.fst.comp hp
  have he := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hp))
  have hc := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hp))
  refine ⟨hp,?_⟩
  exact (ClosedWordDecisionCompletion.MachinePrograms.solve_computable.comp (hd.pair he)).pair
    (Primrec.not.to_comp.comp
      (ClosedWordDecisionCompletion.MachinePrograms.solve_computable.comp (hd.pair hc)))

theorem full : Targets.PolynomialBooleanComparison :=
  ⟨CalibrationProof.full, compilerPrograms, RealizationProof.full,
   SemanticBasics.globalSoundness, DomainsProof.full, ExistentialProof.full, DecisionProof.flags⟩

end LogicLineages.StandardControlCurrent.PolynomialBoolean.Proof
