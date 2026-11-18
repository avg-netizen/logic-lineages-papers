module
public import LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof
public import LogicLineages.OrdinalComparison.SourceSignedPairCombinatorProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessValuesProof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment
open SelectedSourceDomain SelectedHardness SelectedHardnessCoordinatesProof
open SelectedHardnessUnusedProof SelectedHardnessCombinatorSyntaxProof SelectedHardnessPairSyntaxProof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem project_head (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    value1 ctrl p ρ (SelectedHardness.project a b) = projectHead (value1 ctrl p ρ a) (value1 ctrl p ρ b) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := coordinateFacts ctrl K hc Γ p ρ a
  obtain ⟨bv,hb,hb0,hb1,_⟩ := coordinateFacts ctrl K hc Γ p ρ b
  rw [value1_of_assignment ctrl p ρ _ _ (project_assignment p a b av bv ha hb), project_head_expression]
  change ordinalNaturalProduct ((2 : Ordinal)^(ordinalNaturalSum 1 1))
    (ordinalNaturalSum (SelectedHardness.paddedHead (expressionValue ctrl ρ (av 1)))
      (expressionValue ctrl ρ (bv 1))) = _
  rw [Source.SignedPair.Proof.two_power_two,ha1,hb1]
  rfl

theorem combine_head (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    value1 ctrl p ρ (SelectedHardness.combine a b) = combineHead (value1 ctrl p ρ a) (value1 ctrl p ρ b) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := coordinateFacts ctrl K hc Γ p ρ a
  obtain ⟨bv,hb,hb0,hb1,_⟩ := coordinateFacts ctrl K hc Γ p ρ b
  rw [value1_of_assignment ctrl p ρ _ _ (combine_assignment p a b av bv ha hb), combine_head_expression]
  change ordinalNaturalProduct ((2 : Ordinal)^(ordinalNaturalSum 1 1))
    (ordinalNaturalSum (SelectedHardness.paddedHead (expressionValue ctrl ρ (av 1)))
      (SelectedHardness.paddedHead (expressionValue ctrl ρ (bv 1)))) = _
  rw [Source.SignedPair.Proof.two_power_two,ha1,hb1]
  rfl

theorem omega_head (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary) :
    value1 ctrl p ρ (SelectedHardness.liftOmega a) = ordinalNaturalProduct Ordinal.omega0
      (ordinalNaturalSum 1 (SelectedHardness.paddedHead (value1 ctrl p ρ a))) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := coordinateFacts ctrl K hc Γ p ρ a
  rw [value1_of_assignment ctrl p ρ _ _ (omega_assignment p a av ha), omega_head_expression]
  change ordinalNaturalProduct ((2 : Ordinal)^Ordinal.omega0)
    (ordinalNaturalSum 1 (SelectedHardness.paddedHead (expressionValue ctrl ρ (av 1)))) = _
  have hp : (2 : Ordinal)^Ordinal.omega0 = Ordinal.omega0 := by
    simpa using Ordinal.natCast_opow_omega0 (by decide : 1 < (2 : Nat))
  rw [hp,ha1]

theorem combine_scalar (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    value0 ctrl p ρ (SelectedHardness.combine a b) = ParametricActualCollapse.collapseWith ctrl
      (ordinalNaturalProduct Ordinal.omega0 (combineHead (value1 ctrl p ρ a) (value1 ctrl p ρ b)) +
      ((9*value0 ctrl p ρ a+5*value0 ctrl p ρ b+13 : Nat) : Ordinal)) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := coordinateFacts ctrl K hc Γ p ρ a
  obtain ⟨bv,hb,hb0,hb1,_⟩ := coordinateFacts ctrl K hc Γ p ρ b
  apply value0_of_assignment ctrl p ρ _ _ _ (combine_assignment p a b av bv ha hb)
  have hs := SelectedHardnessScalarSyntaxProof.combine_scalar_value ctrl p (valuation ctrl ρ) av bv
    (value0 ctrl p ρ a) (value0 ctrl p ρ b) ha0 hb0
  have hh : ParametricSourceSuccessor.denoteWith ctrl (valuation ctrl ρ) (combineHeadExpr av bv) =
      combineHead (value1 ctrl p ρ a) (value1 ctrl p ρ b) := by
    change ordinalNaturalProduct ((2 : Ordinal)^(ordinalNaturalSum 1 1))
      (ordinalNaturalSum (SelectedHardness.paddedHead (expressionValue ctrl ρ (av 1)))
        (SelectedHardness.paddedHead (expressionValue ctrl ρ (bv 1)))) = _
    rw [Source.SignedPair.Proof.two_power_two,ha1,hb1]
    rfl
  rw [hh,actualNaturalSumFiniteRight] at hs
  exact hs

end LogicLineages.PermittedControl.SelectedHardnessValuesProof
