module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessTargets
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessProof
open PredictionGame PredictionTapeObservation PredictionTapeRuntime PredictionTapeRuntimeClass
open PredictionFiniteChange PredictionTapeFlip PredictionOriginalBounds PredictionOriginalHardness PredictionOriginalHardnessTargets

private theorem runtime_diagonal (g : Nat → Nat → Nat) (m e : Nat)
    (h : EventualRuntime e (levelBound g m)) : EventualRuntime e (diagonal g) := by
  obtain ⟨N, hN⟩ := diagonalDominance g m
  obtain ⟨M, hM⟩ := h
  refine ⟨max N M, fun n hn => ?_⟩
  obtain ⟨t, ht, hb⟩ := hM n (by omega)
  exact ⟨t, ht, lt_of_lt_of_le hb (hN n (by omega))⟩

private theorem negative_witness (g : Nat → Nat → Nat) (hcover : CoversPR g)
    (R : Matrix) (z : Nat) (hn : ¬ MatrixTruth R z) :
    ∃ k : Nat, ∃ he : TotalBinary (evaderCode k),
      EventualRuntime (evaderCode k) (diagonal g) ∧
      ¬ Learns (flipPolicy R (diagonal g) z) (policy (evaderCode k) he) := by
  classical
  change ¬ ∀ k, ∃ s, ∀ t, R (z, k, s, t) = true at hn
  obtain ⟨k, hk⟩ := not_forall.mp hn
  have hinf : (changeSet R z k).Infinite := by
    intro hfin
    exact hk ((PredictionFiniteChangeProof.finiteChangesIffWitness R z k).1 hfin)
  obtain ⟨he, heq⟩ := PredictionTapeRuntimeClassProof.exactEvaderPolicy k
  have htime := (PredictionTapeRuntimeClassProof.exactEvaderMembership k (diagonal g)).2
    (evaderDiagonalTail g hcover k)
  have hav := (PredictionTapeRuntimeClassProof.exactAvailabilityCalibration (evaderCode k) he (diagonal g)).2 htime
  exact ⟨k, he, htime, PredictionTapeFlipProof.negativeTapeFlipLearning R (diagonal g) z k hinf
    (evaderCode k) he heq hav⟩

theorem simultaneousOriginalReduction : SimultaneousOriginalReduction := by
  classical
  intro g hlisting
  rcases hlisting with ⟨hg, _, hcover⟩
  obtain ⟨m₀, hm₀, hlevels⟩ := evaderLevelTail g hcover
  refine ⟨m₀, hm₀, ?_⟩
  intro R hR
  obtain ⟨f, hf, hprog⟩ := PredictionTapeFlipProof.uniformTapeFlipProgram R (diagonal g) hR (computableBounds g hg).2
  choose hp hpid using hprog
  refine ⟨f, hf, hp, ?_⟩
  intro z
  rw [hpid z]
  have good : MatrixTruth R z → Threshold (flipPolicy R (diagonal g) z) (diagonal g) := by
    intro htruth e he htime
    exact PredictionTapeFlipProof.positiveTapeFlipLearning R (diagonal g) z
      (fun k => (PredictionFiniteChangeProof.finiteChangesIffWitness R z k).2 (htruth k)) e he
      ((PredictionTapeRuntimeClassProof.exactAvailabilityCalibration e he (diagonal g)).2 htime)
  have good_level : ∀ m, MatrixTruth R z → Threshold (flipPolicy R (diagonal g) z) (levelBound g m) := by
    intro m htruth e he htime
    exact good htruth e he (runtime_diagonal g m e htime)
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro ht
      by_contra hn
      obtain ⟨k, he, htime, hnot⟩ := negative_witness g hcover R z hn
      exact hnot (ht (evaderCode k) he htime)
    · exact good
  · change PredictionTapeMeasureContract.height (levelBound g) (flipPolicy R (diagonal g) z) = ⊤ ↔ _
    constructor
    · intro htop
      by_contra hn
      obtain ⟨k, he, _, hnot⟩ := negative_witness g hcover R z hn
      have ht := (PredictionTapeMeasureContractProof.infiniteCharacterization _ _).1 htop m₀ hm₀
      have htime := (PredictionTapeRuntimeClassProof.exactEvaderMembership k (levelBound g m₀)).2
        (hlevels m₀ le_rfl k)
      exact hnot (ht (evaderCode k) he htime)
    · intro htruth
      exact (PredictionTapeMeasureContractProof.infiniteCharacterization _ _).2
        (fun m _ => good_level m htruth)
  · intro m hm
    constructor
    · intro ht
      by_contra hn
      obtain ⟨k, he, _, hnot⟩ := negative_witness g hcover R z hn
      have htime := (PredictionTapeRuntimeClassProof.exactEvaderMembership k (levelBound g m)).2
        (hlevels m hm k)
      exact hnot (ht (evaderCode k) he htime)
    · exact good_level m

theorem wholeSourceHardness : WholeSourceHardness :=
  ⟨PredictionTapeHardnessProof.fixedBudgetHardness, simultaneousOriginalReduction⟩

theorem infiniteOriginalPredictor : InfiniteOriginalPredictor := by
  intro g hg
  obtain ⟨_, _, h⟩ := simultaneousOriginalReduction g hg
  obtain ⟨f, _, hp, hs⟩ := h (fun _ => true) (Computable.const true)
  refine ⟨f 0, hp 0, (hs 0).2.1.2 ?_⟩
  intro k
  exact ⟨0, fun _ => rfl⟩

end LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessProof
