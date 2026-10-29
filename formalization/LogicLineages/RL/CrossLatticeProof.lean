module

public import LogicLineages.RL.CrossTargets
public import LogicLineages.RL.PolicySemanticsProof
public import Mathlib.Topology.Instances.Int
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace LogicLineages.RL.Policy.CrossLatticeProof

open Filter Topology

theorem denominator_pos (d : PositiveDenominator) : (0 : ℝ) < (d.val : ℝ) := by
  exact_mod_cast d.property

theorem latticeLimit (d : PositiveDenominator) : Targets.LatticeLimit d := by
  intro f v hf hv
  have hd := denominator_pos d
  have hmem : v * (d.val : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) := by
    apply Int.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto (hv.mul_const (d.val : ℝ))
    exact Filter.Eventually.of_forall fun n => by
      obtain ⟨z, hz⟩ := hf n
      refine ⟨z, ?_⟩
      rw [hz, div_mul_cancel₀ _ (ne_of_gt hd)]
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, (eq_div_iff (ne_of_gt hd)).mpr hz.symm⟩

theorem latticeRewardLimit (d : PositiveDenominator) : Targets.LatticeRewardLimit d := by
  classical
  intro rewards v hr hv
  apply latticeLimit d _ v _ hv
  choose z hz using hr
  intro n
  refine ⟨∑ i ∈ Finset.range n, z i, ?_⟩
  simp only [hz, Int.cast_sum, Finset.sum_div]

theorem deterministicRewardLattice (F : LogicLineages.RL.Framework) (d : PositiveDenominator) :
    Targets.DeterministicRewardLattice F d := by
  rintro ⟨rewards, hr, hv⟩ p μ
  exact latticeRewardLimit d (rewards p μ) (F.value p μ) (hr p μ) (hv p μ)

theorem ddIntegerValue (S : Alphabet) : Targets.DDIntegerValue S := by
  intro p μ
  have hf : ∀ n, ∃ z : ℤ,
      finiteValue (embedPolicy p) (embedEnvironment μ.val) n = (z : ℝ) / (1 : ℝ) := by
    intro n
    cases n with
    | zero => exact ⟨0, by simpa using (PolicySemanticsProof.initialHorizonCalibration S _ _).1⟩
    | succ n =>
        refine ⟨positiveReward n (deterministicTrace p μ.val n []), ?_⟩
        simpa using (PolicySemanticsProof.deterministicCalibration S).2.2.2 p μ.val n
  obtain ⟨z, hz⟩ := latticeLimit ⟨1, by decide⟩ _ _
    (by simpa [admissibleEmbedEnvironment] using hf)
    (PolicySemanticsProof.valueLimit S (embedPolicy p) (admissibleEmbedEnvironment μ)).1
  exact ⟨z, by simpa using hz⟩

theorem scaledDDCalibration (S : Alphabet) (d : PositiveDenominator) :
    Targets.ScaledDDCalibration S d := by
  constructor
  · intro p μ
    obtain ⟨z, hz⟩ := ddIntegerValue S p μ
    exact ⟨z, congrArg (fun x : ℝ => x / (d.val : ℝ)) hz⟩
  · intro p μ
    constructor
    · exact (PolicySemanticsProof.valueLimit S (embedPolicy p)
        (admissibleEmbedEnvironment μ)).1.div_const (d.val : ℝ)
    · intro n
      unfold scaledFiniteValue finiteValue
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro tr htr
      ring

end LogicLineages.RL.Policy.CrossLatticeProof
