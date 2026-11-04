module
public import LogicLineages.OrdinalComparison.SourcePolynomialGradeOneConstructionProof
public import LogicLineages.OrdinalComparison.SourcePolynomialRealizationProof
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialGradeOne.Proof
open OriginalDomain

private theorem signedCNF_injective : Function.Injective SignedPair.signedCNF := by
  intro a b hab
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  have h := congrArg (fun g : SignedPair.CantorGroup => g e) hab
  simp only [SignedPair.Proof.cnf_apply] at h
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite b e)
  rw [hm,hn,SignedPair.Proof.finite_nat,SignedPair.Proof.finite_nat] at h
  have he : m=n := by exact_mod_cast h
  rw [hm,hn,he]

theorem actualGradedRealization : Targets.ActualGradedRealization := by
  intro p hp
  obtain ⟨t,ht,hcnf⟩ := gradedConstruction p hp
  obtain ⟨a,ha,hac,hproj,hzero,hpos⟩ := SourcePolynomialRealization.Proof.actualRealization p
  have he : closedValue t=a := signedCNF_injective (hcnf.trans hac.symm)
  refine ⟨t,ht,hcnf,?_,?_⟩
  · rw [he]
    exact hpos.mpr hp
  · rw [he]
    exact ha
end LogicLineages.OrdinalComparison.Source.SourcePolynomialGradeOne.Proof
