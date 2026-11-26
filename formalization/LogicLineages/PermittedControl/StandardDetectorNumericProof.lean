module
public import LogicLineages.PermittedControl.StandardDetectorNumericTargets
public import LogicLineages.PermittedControl.StandardSourceFactsProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorOmegaOrderProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardDetectorNumeric.Proof
open OrdinalComparison Source ParametricActualCollapse

 theorem calibration : Calibration := by
  refine ⟨ParametricSourceSuccessor.Proof.phi_global,?_⟩
  intro h s q
  exact ParametricSourceSuccessor.Proof.phi_global _

 theorem finiteTails : FiniteTails := by
  refine ⟨?_,?_,?_⟩
  · intro a ha s t hst
    simpa only [ParametricSourceSuccessor.Proof.phi_global] using
      actualCollapseFiniteTailMonotone a ha s t hst
  · intro a ha hl n
    simpa only [ParametricSourceSuccessor.Proof.phi_global] using
      FunctionalDetector.Proof.tail_two_fourfold a ha hl n
  · intro a ha hl s t q hst
    simpa only [ParametricSourceSuccessor.Proof.phi_global] using
      FunctionalDetector.Proof.tail_gap_fourfold a ha hl s t q hst

 theorem headBudget : HeadBudget := by
  intro a b s t q ha hb hal hbl hab hn hs hq
  have hα := actualFiniteTailClosureNorm a ha (s+q+2)
  have hβ := actualFiniteTailClosureNorm b hb (t+q)
  refine ⟨?_,?_⟩
  · rw [hα.2,hβ.2]
    calc
      actualOrdinalNorm a+(s+q+2) ≤ 4*q+2 := by omega
      _ ≤ 2^(q+1) := FunctionalDetector.Proof.four_linear_le_power q hq
      _ ≤ 2^(actualOrdinalNorm b+(t+q)+100) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ Phi (actualOrdinalNorm b+(t+q)) := two_pow_shift_le_Phi _
  · simpa only [ParametricSourceSuccessor.Proof.phi_global] using
      FunctionalDetector.Proof.head_domination a b s t q ha hb hal hbl hab hn hs hq

 theorem sourceHeadSeparation : SourceHeadSeparation := by
  intro Γ policy ρ a b q hab hs hq
  obtain ⟨av,hav,ha0,ha1,hap0,hap1,hae,han⟩ :=
    StandardSourceFacts.Proof.unaryFacts Γ policy ρ a
  obtain ⟨bv,hbv,hb0,hb1,hbp0,hbp1,hbe,hbn⟩ :=
    StandardSourceFacts.Proof.unaryFacts Γ policy ρ b
  have h := FunctionalDetector.Proof.app_strict_head
    (SelectedHardness.value1 Phi policy ρ a) (SelectedHardness.value1 Phi policy ρ b)
    (SelectedHardness.value0 Phi policy ρ a) (SelectedHardness.value0 Phi policy ρ b) q
    hap1 hae hbe hab han hs hq
  simpa only [appValue,FunctionalDetector.Proof.appValue,
    ParametricSourceSuccessor.Proof.phi_global] using h

 theorem sourceScalarSeparation : SourceScalarSeparation := by
  intro Γ policy ρ a b q hab hs
  obtain ⟨av,hav,ha0,ha1,hap0,hap1,hae,han⟩ :=
    StandardSourceFacts.Proof.unaryFacts Γ policy ρ a
  have he := FunctionalDetector.Proof.omega_product_below _ hae
  have hl := FunctionalDetector.Proof.omega_product_limit _ hap1 hae
  have h := finiteTails.2.2 _ he hl
    (SelectedHardness.value0 Phi policy ρ a) (SelectedHardness.value0 Phi policy ρ b) q hs
  change 4*appValue (SelectedHardness.value1 Phi policy ρ a)
    (SelectedHardness.value0 Phi policy ρ a) q <
    appValue (SelectedHardness.value1 Phi policy ρ b) (SelectedHardness.value0 Phi policy ρ b) q
  unfold appValue
  rw [← hab]
  exact h

 theorem standardDetectorNumeric : StandardDetectorNumeric :=
  ⟨calibration,finiteTails,headBudget,sourceHeadSeparation,sourceScalarSeparation⟩
end LogicLineages.PermittedControl.StandardDetectorNumeric.Proof
