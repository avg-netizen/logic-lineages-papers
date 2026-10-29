module

public import LogicLineages.ComputabilityKnowledge.Comparators.PolynomialComparisonEffectivity
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitEffectivityProof
public import LogicLineages.ComputabilityKnowledge.CircuitComparisonEffectivityProof

@[expose] public section

/-! External Codex continuation: actual primitive-recursive certificates for
both literal Option.bind compositions, with exact orientation correspondence. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialComparisonEffectivityProof

open PolynomialCircuit PolynomialComparison

theorem outputCodecFaithful : Comparators.PolynomialComparisonEffectivity.OutputCodecFaithful :=
  CircuitComparisonEffectivityProof.outputCodecFaithful

theorem strictCorrespondence : Comparators.PolynomialComparisonEffectivity.StrictCorrespondence := by
  intro p
  unfold PolynomialComparison.strictCode
  rw [PolynomialCircuitEffectivityProof.codeCorrespondence p]
  simp only [Option.bind_some]
  exact CircuitComparisonEffectivityProof.strictCorrespondence (PolynomialCircuit.compile p)

theorem weakCorrespondence : Comparators.PolynomialComparisonEffectivity.WeakCorrespondence := by
  intro p
  unfold PolynomialComparison.weakCode
  rw [PolynomialCircuitEffectivityProof.codeCorrespondence p]
  simp only [Option.bind_some]
  exact CircuitComparisonEffectivityProof.weakCorrespondence (PolynomialCircuit.compile p)

theorem strictPrimrec : Primrec PolynomialComparison.strictCode :=
  Primrec.option_bind PolynomialCircuitEffectivityProof.compilerPrimrec
    (CircuitComparisonEffectivityProof.strictPrimrec.comp Primrec.snd).to₂

theorem weakPrimrec : Primrec PolynomialComparison.weakCode :=
  Primrec.option_bind PolynomialCircuitEffectivityProof.compilerPrimrec
    (CircuitComparisonEffectivityProof.weakPrimrec.comp Primrec.snd).to₂

theorem polynomialComparisonEffectivity : Comparators.PolynomialComparisonEffectivity.Target :=
  ⟨outputCodecFaithful,strictCorrespondence,weakCorrespondence,strictPrimrec.to_comp,weakPrimrec.to_comp⟩

end LogicLineages.ComputabilityKnowledge.PolynomialComparisonEffectivityProof
