module
public import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.Targets
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.MRDPFamilyProof
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ProgramsProof
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ScalarSemanticProof
import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.ScalarUpperBoundProof

public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.GlobalProof
open DiophantineCompletion.Specialization

/-- Specialize one fixed representing polynomial and run the actual
depth-two compiler. The same well-formed output proves both original value
comparison and original norm comparison, on every input of the reduction. -/
theorem scalarHardness : Targets.ScalarHardness := by
  intro weak P hP
  obtain ⟨m,p,_,_,hwell,hcompute,hcode,hroot⟩ :=
    MRDPFamilyProof.rePolynomialFamily P hP
  refine ⟨fun x => scalarProgram weak (specializationCode p x),
    (ProgramsProof.scalarPrograms weak).comp hcompute,?_⟩
  intro x
  change ScalarDomain (scalarProgram weak (specializationCode p x)) ∧
    (¬ P x ↔ ScalarComparison false weak (scalarProgram weak (specializationCode p x))) ∧
    (¬ P x ↔ ScalarComparison true weak (scalarProgram weak (specializationCode p x)))
  rw [hcode x, ProgramsProof.scalarCalibration]
  have hbridge := ScalarSemanticProof.polynomialSourceBridge
    (specialize x p) (hwell x) weak
  exact ⟨hbridge.1,
    (not_congr (hroot x)).trans (hbridge.2 false),
    (not_congr (hroot x)).trans (hbridge.2 true)⟩

theorem scalarCompleteness : Targets.ScalarCompleteness := by
  intro norm weak
  refine ⟨ScalarUpperBoundProof.scalarUpperBound norm weak,?_⟩
  intro P hP
  obtain ⟨f,hcompute,hcorrect⟩ := scalarHardness weak P hP
  refine ⟨f,hcompute,?_⟩
  intro x
  cases norm with
  | false => exact (hcorrect x).2.1
  | true => exact (hcorrect x).2.2

/-- Whole paper02 thm:finite-bare-hardness, retaining both order symbols,
both value/norm comparisons, every finite ground context, the original
admissible substitution domain, and the literal depth-two syntax. -/
theorem fullFiniteBareHardness : Targets.FullFiniteBareHardness :=
  ⟨scalarHardness,scalarCompleteness,ScalarSemanticProof.positiveSourceFacts⟩

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.GlobalProof
