module

public import LogicLineages.RL.ClassificationTargets
public import LogicLineages.RL.SeparatorProof
public import LogicLineages.RL.PositiveTransformationProof

@[expose] public section

namespace LogicLineages.RL.Policy.NegativeTransformationProof

open PositiveTransformationProof

noncomputable def midpointWeight : RatOpenUnit := ⟨1 / 2, by constructor <;> norm_num⟩

theorem negativeTransformation (S : Alphabet) : Targets.NegativeTransformation S := by
  classical
  intro sourceEnv targetEnv hT
  obtain ⟨T⟩ := hT
  obtain ⟨p, q, μ, hpq⟩ := T.agentsSeparated
  change value (embedPolicy (T.agentMap p)) (environmentKernel targetEnv μ) <
    value (embedPolicy (T.agentMap q)) (environmentKernel targetEnv μ) at hpq
  obtain ⟨η, C, hrange, hneq⟩ := SeparatorProof.twoValueSeparator S
    (T.agentMap p) (T.agentMap q) (environmentKernel targetEnv μ) (ne_of_lt hpq)
  let ηTarget : Environment S targetEnv := liftEnvironment targetEnv η
  let ν : AdmissibleSEnvironment S := environmentKernel sourceEnv (T.environmentMap ηTarget)
  let v : SPolicy S → ℝ := fun r =>
    value (embedPolicy (T.agentMap r)) (admissibleEmbedEnvironment η)
  have hf (r s : SPolicy S) : v r < v s ↔ value r ν < value s ν := by
    have h := T.faithful r s ηTarget
    change (value (embedPolicy (T.agentMap r)) (environmentKernel targetEnv ηTarget) <
      value (embedPolicy (T.agentMap s)) (environmentKernel targetEnv ηTarget)) ↔
      (value r ν < value s ν) at h
    dsimp only [ηTarget] at h
    rw [liftEnvironment_kernel] at h
    exact h
  have no_between (r u s : SPolicy S) (hru : v r < v u) (hus : v u < v s) : False := by
    have hr := hrange (T.agentMap r)
    have hu := hrange (T.agentMap u)
    have hs := hrange (T.agentMap s)
    change v r = (C : ℝ) ∨ v r = (C : ℝ) + 1 at hr
    change v u = (C : ℝ) ∨ v u = (C : ℝ) + 1 at hu
    change v s = (C : ℝ) ∨ v s = (C : ℝ) + 1 at hs
    rcases hr with hr | hr <;> rcases hu with hu | hu <;> rcases hs with hs | hs <;> linarith
  let a₀ : S.Action := Classical.choice S.actionNonempty
  let m : SPolicy S := behavioralMixture a₀ midpointWeight p q
  have hm : value m ν = (value p ν + value q ν) / 2 := by
    rw [MixtureProof.behavioralMixtureValue S a₀ midpointWeight p q ν]
    norm_num [midpointWeight]
    ring
  change v p ≠ v q at hneq
  rcases lt_or_gt_of_ne hneq with h | h
  · have hs := (hf p q).mp h
    exact no_between p m q ((hf p m).mpr (by linarith)) ((hf m q).mpr (by linarith))
  · have hs := (hf q p).mp h
    exact no_between q m p ((hf q m).mpr (by linarith)) ((hf m p).mpr (by linarith))

end LogicLineages.RL.Policy.NegativeTransformationProof
