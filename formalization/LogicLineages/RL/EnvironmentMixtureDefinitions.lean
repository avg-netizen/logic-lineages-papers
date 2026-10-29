module

public import LogicLineages.RL.MixtureDefinitions

/-! Actual initial environment mixtures for paper 13 `prop:cross` and its
following paragraph. Branch likelihoods contain past percept probabilities,
not action probabilities. No final action is added to a horizon trace. -/
@[expose] public section

namespace LogicLineages.RL.Policy

def perceptHistoryLikelihood {S : Alphabet} (μ : SEnvironment S) (h : EnvHistory S) : ℚ :=
  ∏ i : Fin h.length, (μ (h.take i.val)).mass (h.get i).1

def environmentMixtureDenominator {S : Alphabet} (w : RatOpenUnit)
    (μ ν : SEnvironment S) (h : EnvHistory S) : ℚ :=
  w.val * perceptHistoryLikelihood μ h + (1 - w.val) * perceptHistoryLikelihood ν h

def environmentPosteriorWeight {S : Alphabet} (w : RatOpenUnit)
    (μ ν : SEnvironment S) (h : EnvHistory S) : RatUnit := by
  let d := environmentMixtureDenominator w μ ν h
  have hp : 0 ≤ perceptHistoryLikelihood μ h :=
    Finset.prod_nonneg (fun i _ => (μ (h.take i.val)).nonneg (h.get i).1)
  have hq : 0 ≤ perceptHistoryLikelihood ν h :=
    Finset.prod_nonneg (fun i _ => (ν (h.take i.val)).nonneg (h.get i).1)
  have hwp : 0 ≤ w.val * perceptHistoryLikelihood μ h := mul_nonneg w.property.1.le hp
  have hwq : 0 ≤ (1 - w.val) * perceptHistoryLikelihood ν h :=
    mul_nonneg (sub_nonneg.mpr w.property.2.le) hq
  exact if hd : 0 < d then
    ⟨w.val * perceptHistoryLikelihood μ h / d, div_nonneg hwp hd.le,
      (div_le_one hd).mpr (le_add_of_nonneg_right hwq)⟩
    else zeroWeight

noncomputable def environmentMixture {S : Alphabet} (w : RatOpenUnit)
    (μ ν : SEnvironment S) : SEnvironment S :=
  fun h => if 0 < environmentMixtureDenominator w μ ν h then
    kernelMix (environmentPosteriorWeight w μ ν h) (ν h) (μ h)
  else dirac S.zeroPercept

end LogicLineages.RL.Policy
