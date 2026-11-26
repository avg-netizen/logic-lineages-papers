module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseMainTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseAssemblyProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightEffectiveProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16UniformEffectiveCodedProof
public import LogicLineages.PersistentMarking.OrdinalOmegaOrbitProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ActualCollapseMain
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerTargets NativeTowerSequenceTargets
open ExternalOrdinalInterfaceTargets ConditionalHeightTargets ConditionalHeightEffectiveTargets
open ConditionalMain16UniformEffectiveCodedTargets ActualCollapse

theorem solutionExists : SolutionExists := by
  obtain ⟨Z, s, add, mul, h1⟩ := OrdinalArithmeticOrbitProof.exact_OrdinalArithmeticOrbits
  obtain ⟨w, one, pow, fix, h2, _⟩ := OrdinalOmegaOrbitProof.exact_OrdinalOmegaOrbits Z s add mul h1
  exact ⟨Z, s, add, mul, w, one, pow, fix, h1, h2⟩

theorem actualTowerCofinality : ActualTowerCofinality := by
  intro Z s add mul w one pow fix h1 h2
  have sup := actualTowerSupremum Z s add mul w one pow fix h1 h2
  exact ⟨sup, fun BH hBH => sup.trans hBH⟩

theorem actualHeightEffective : ActualHeightEffective := by
  intro Z s add mul w one pow fix h1 h2 BH calibration endpoint upper
  exact ConditionalHeightEffectiveProof.conditionalHeightEffective ActualIndex (veblenData fix pow w) BH
    calibration (actualTowerHypotheses Z s add mul w one pow fix h1 h2) endpoint upper

theorem actualMain16 : ActualMain16 := by
  intro Z s add mul w one pow fix h1 h2 BH norm uniform calibration endpoint
  exact ConditionalMain16UniformEffectiveCodedProof.exact_ConditionalMain16UniformEffectiveCoded
    ActualIndex (veblenData fix pow w) BH norm uniform calibration
    (actualTowerHypotheses Z s add mul w one pow fix h1 h2) endpoint

theorem calibrationFirstInstances : CalibrationFirstInstances := by
  intro Z s add mul w one pow fix h1 h2
  let N := veblenValue fix pow
  let Γ := baseValue fix pow w
  obtain ⟨infl, hΓ⟩ := veblenInflationary Z s add mul w one pow fix h1 h2
  have char : CharacterizationP (actualData N Γ) := actualCharacterization N Γ infl hΓ
  obtain ⟨aboveOne, _, _, _⟩ := criticalFacts N Γ infl hΓ
  let z := mkCountable 0 zero_lt_omegaOne
  have oz : orbit .base N Γ z = Γ := orbit_zero N Γ z rfl
  let o1 := mkCountable 1 one_lt_index
  have o1eq : orbit .base N Γ o1 = N Γ := by
    rw [(orbitEquations .base N Γ).2.1 z o1 (by show (1 : Ordinal.{0}) = 0 + 1; simp), oz]
  have critGe : ∀ θ, Critical N Γ θ → Γ.val ≤ θ := by
    rintro θ ⟨α, rfl⟩
    have := orbit_mono N Γ infl (α := z) (β := α) (show (0 : Ordinal.{0}) ≤ α.val from not_lt.mp not_lt_zero)
    rwa [oz] at this
  have arg0 : argument 0 = 0 := exact_LiteralRecurrence.2.1
  have arg1 : argument 1 = 1 := exact_LiteralRecurrence.2.2.1
  -- ψ(0) = Γ
  have psi0 : (actualData N Γ).psi (actualArgument 0) = Γ.val := by
    refine le_antisymm ((char (actualArgument 0)).2.2 Γ.val ⟨z, by rw [oz]⟩ (fun η hη _ => ?_))
      (critGe _ (char (actualArgument 0)).1)
    have : η.val < argument 0 := hη
    rw [arg0] at this
    exact (not_lt_zero this).elim
  -- ψ(1) = N_B(Γ)
  have psi1 : (actualData N Γ).psi (actualArgument 1) = (N Γ).val := by
    have only0 : ∀ η : ActualIndex, η < actualArgument 1 → η = actualArgument 0 := by
      intro η hη
      have : η.val < argument 1 := hη
      rw [arg1, Ordinal.lt_one_iff_zero] at this
      exact Subtype.ext (this.trans arg0.symm)
    refine le_antisymm ((char (actualArgument 1)).2.2 (N Γ).val ⟨o1, by rw [o1eq]⟩ (fun η hη _ => ?_)) ?_
    · rw [only0 η hη, psi0]
      exact infl Γ
    · obtain ⟨hc, hcl, _⟩ := char (actualArgument 1)
      have lt01 : actualArgument 0 < actualArgument 1 :=
        show argument 0 < argument 1 from exact_StrictlyIncreasing (Nat.lt_succ_self 0)
      have normLt : actualNorm (actualArgument 0) < (actualData N Γ).psi (actualArgument 1) :=
        lt_of_le_of_lt (normBound 0) (aboveOne _ hc)
      have gt : Γ.val < (actualData N Γ).psi (actualArgument 1) := by
        have := hcl (actualArgument 0) lt01 normLt
        rwa [psi0] at this
      obtain ⟨α, hα⟩ := hc
      rw [← hα] at gt ⊢
      have hα0 : α.val ≠ 0 := by
        intro h0
        rw [orbit_zero N Γ α h0] at gt
        exact lt_irrefl _ gt
      have : o1.val ≤ α.val := Order.one_le_iff_ne_zero.2 hα0
      have := orbit_mono N Γ infl this
      rwa [o1eq] at this
  exact ⟨psi0.symm, psi1.symm⟩

#print axioms solutionExists
#print axioms actualTowerCofinality
#print axioms actualHeightEffective
#print axioms actualMain16
#print axioms calibrationFirstInstances

end LogicLineages.PersistentMarking.ActualCollapseMain
