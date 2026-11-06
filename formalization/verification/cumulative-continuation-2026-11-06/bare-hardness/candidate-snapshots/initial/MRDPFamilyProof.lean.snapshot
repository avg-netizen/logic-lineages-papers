module
public import LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.MRDPFamilyTargets
import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ReductionProof
import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityProof

public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.MRDPFamilyProof
open DiophantineCompletion DiophantineCompletion.Specialization

/-- The construction is the same fixed-code specialization used in the
accepted REPolynomialReduction proof. Its well-formedness and canonical-code
facts remain visible here so downstream reductions never need to interpret
an arbitrary malformed polynomial code. -/
theorem rePolynomialFamily : MRDPFamilyTargets.REPolynomialFamily := by
  intro P hP
  have hD := ReductionProof.rePredicateDiophantine P hP
  obtain ⟨m,p,hpn,hpw,hrep⟩ :=
    (DiophantinePolynomialBridgeProof.diophantineCodeRepresentation 1
      {v : Fin 1 → Nat | P (v 0)}).1 hD
  have harity : p.inputCount = m + 1 := by omega
  refine ⟨m,p,harity,hpw,?_,?_,?_,?_⟩
  · intro x
    exact SpecializationSemanticProof.substitutionWellFormed p x hpw
  · exact (SpecializationCodeProof.specializationCodePrimrec p).to_comp
  · exact SpecializationCodeProof.specializationCodeCalibration p
  · intro x
    rw [SpecializationSemanticProof.substitutionRootCorrespondence p m x harity]
    exact hrep (fun _ : Fin 1 => x)

theorem haltingObstruction : MRDPFamilyTargets.HaltingObstruction :=
  ⟨UndecidabilityProof.natHaltingRE, UndecidabilityProof.natHaltingUndecidable⟩

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.MRDPFamilyProof
