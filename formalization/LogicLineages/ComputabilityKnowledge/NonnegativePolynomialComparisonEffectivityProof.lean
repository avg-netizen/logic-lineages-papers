module

public import LogicLineages.ComputabilityKnowledge.Comparators.NonnegativePolynomialComparisonEffectivity
public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftEffectivityProof
public import LogicLineages.ComputabilityKnowledge.PolynomialComparisonEffectivityProof

@[expose] public section

/-! External Codex continuation: certificates for both literal encoded
compositions. Actual primitive recursion implies the frozen Computable claims. -/
namespace LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparisonEffectivityProof

open PolynomialCircuit PolynomialDomainShift NonnegativePolynomialComparison

theorem outputCodecFaithful : Comparators.NonnegativePolynomialComparisonEffectivity.OutputCodecFaithful :=
  PolynomialComparisonEffectivityProof.outputCodecFaithful

theorem strictCorrespondence : Comparators.NonnegativePolynomialComparisonEffectivity.StrictCorrespondence := by
  intro p
  unfold NonnegativePolynomialComparison.strictCode
  rw [PolynomialDomainShiftEffectivityProof.codeCorrespondence p]
  simp only [Option.bind_some]
  exact PolynomialComparisonEffectivityProof.strictCorrespondence (shift p)

theorem weakCorrespondence : Comparators.NonnegativePolynomialComparisonEffectivity.WeakCorrespondence := by
  intro p
  unfold NonnegativePolynomialComparison.weakCode
  rw [PolynomialDomainShiftEffectivityProof.codeCorrespondence p]
  simp only [Option.bind_some]
  exact PolynomialComparisonEffectivityProof.weakCorrespondence (shift p)

theorem strictPrimrec : Primrec NonnegativePolynomialComparison.strictCode :=
  Primrec.option_bind PolynomialDomainShiftEffectivityProof.shiftPrimrec
    (PolynomialComparisonEffectivityProof.strictPrimrec.comp Primrec.snd).to₂

theorem weakPrimrec : Primrec NonnegativePolynomialComparison.weakCode :=
  Primrec.option_bind PolynomialDomainShiftEffectivityProof.shiftPrimrec
    (PolynomialComparisonEffectivityProof.weakPrimrec.comp Primrec.snd).to₂

theorem nonnegativePolynomialComparisonEffectivity : Comparators.NonnegativePolynomialComparisonEffectivity.Target :=
  ⟨outputCodecFaithful,strictCorrespondence,weakCorrespondence,strictPrimrec.to_comp,weakPrimrec.to_comp⟩

end LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparisonEffectivityProof
