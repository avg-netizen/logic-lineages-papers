module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ReductionTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.OrdinaryCodeProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationSemanticProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationCodeProof
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitEffectivityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ReductionProof
open Dioph ReductionTargets RowPackingClosureProof Specialization DiophantinePolynomialBridge

theorem rePredicateDiophantine : REPredicateDiophantine := by
  intro P hP
  let u : Nat →. Unit := fun x => Part.assert (P x) (fun _ => Part.some ())
  let f : Nat →. Nat := fun x => (u x).map (fun _ => 0)
  have hu : Partrec u := hP
  have hf : Partrec f := hu.map (Computable.const (0 : Nat)).to₂
  have hg := OrdinaryCodeProof.partrecGraphDiophantine f (Partrec.nat_iff.1 hf)
  have h := finCompose hg ![(fun v : Fin 1 → Nat => v 0),(fun _ => 0)] (by
    intro i
    fin_cases i
    · exact Dioph.proj_dioph 0
    · exact Dioph.const_dioph 0)
  apply h.ext
  intro v
  change 0 ∈ f (v 0) ↔ P (v 0)
  simp [f,u,Part.mem_map_iff,Part.mem_assert_iff,Part.mem_some_iff]

theorem encodedCodeRoot : EncodedCodeRoot := by
  intro p hp
  constructor
  · rintro ⟨xs,q,hxs,hq,_,hr⟩
    have hx : xs = PolynomialCircuit.encode p :=
      Option.some.inj (hxs.symm.trans (Encodable.encodek _))
    subst xs
    have hqp : q = p := Option.some.inj
      (hq.symm.trans (PolynomialCircuitEffectivityProof.inputCodecFaithful p))
    subst q
    exact hr
  · intro hr
    exact ⟨PolynomialCircuit.encode p,p,Encodable.encodek _,
      PolynomialCircuitEffectivityProof.inputCodecFaithful p,hp,hr⟩

/-- The finite representing code is chosen once for fixed P. The runtime
reduction is the explicit, proved primitive-recursive specializationCode p.
No algorithm extracting p from an extensional proof is used or asserted. -/
theorem rePolynomialReduction : Targets.REPolynomialReduction := by
  intro P hP
  have hD := rePredicateDiophantine P hP
  obtain ⟨m,p,hpn,hpw,hrep⟩ :=
    (DiophantinePolynomialBridgeProof.diophantineCodeRepresentation 1
      {v : Fin 1 → Nat | P (v 0)}).1 hD
  refine ⟨specializationCode p,(SpecializationCodeProof.specializationCodePrimrec p).to_comp,?_⟩
  intro x
  rw [SpecializationCodeProof.specializationCodeCalibration]
  rw [encodedCodeRoot (specialize x p) (SpecializationSemanticProof.substitutionWellFormed p x hpw)]
  rw [SpecializationSemanticProof.substitutionRootCorrespondence p m x (by omega)]
  exact hrep (fun _ : Fin 1 => x)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ReductionProof
