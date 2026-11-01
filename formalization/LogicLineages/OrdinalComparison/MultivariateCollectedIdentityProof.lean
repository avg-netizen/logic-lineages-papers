module
public import LogicLineages.OrdinalComparison.MultivariateCollectedIdentityTargets
public import LogicLineages.OrdinalComparison.MultivariateCollectedSourceProof
public import LogicLineages.OrdinalComparison.PositiveUnaryIdentityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateCollected

theorem common_signature_identity : Targets.MultivariateCollectedCommonSignatureIdentity := by
  intro d cap E F hE hF hcE hcF
  constructor
  · intro hn rho _
    have he := source_semantics d cap E hE hcE rho
    have hf := source_semantics d cap F hF hcF rho
    rw [hn] at he
    exact he.symm.trans hf
  · intro hu
    let PE := multivariatePositiveProbe cap E
    let PF := multivariatePositiveProbe cap F
    have hpE : fixedLimitProfileBelow epsilonZero PE := MultivariateFreshProbe.source.1 d cap E hE
    have hpF : fixedLimitProfileBelow epsilonZero PF := MultivariateFreshProbe.source.1 d cap F hF
    have heq : ∀ x : Nat, 0<x → actualFixedLimitProfileEval PE x=actualFixedLimitProfileEval PF x := by
      intro x _
      rw [MultivariateFreshProbe.source.2.1 cap x E,MultivariateFreshProbe.source.2.1 cap x F]
      exact hu _ (fun i _ => MultivariateFreshProbe.head_source.2.2 cap i x)
    have hflag := (actualPositiveUnaryIdentity.2.2.2 PE PF hpE hpF).2.2.2.1.mpr heq
    have hn := (positiveNormalFlagCorrect PE PF hpE hpF).mp hflag
    exact congrArg (decodeMultivariateCollected cap) hn

end LogicLineages.OrdinalComparison.MultivariateCollected
