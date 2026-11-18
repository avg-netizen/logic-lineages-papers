module
public import LogicLineages.PermittedControl.StandardCombinatorCoordinatesTargets
public import LogicLineages.PermittedControl.StandardSourceFactsProof
public import LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof
public import LogicLineages.OrdinalComparison.SourceSignedPairCombinatorProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardCombinatorCoordinates.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment
open SelectedSourceDomain SelectedHardness
open SelectedHardnessUnusedProof SelectedHardnessCombinatorSyntaxProof SelectedHardnessPairSyntaxProof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
theorem value0_of_assignment {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary)
    (v : OrdinalVector Γ 1) (n : Nat) (ha : assignment p a = some v)
    (hn : expressionValue ctrl ρ (v 0) = (n : Ordinal)) : value0 ctrl p ρ a = n := by
  unfold value0
  rw [ha]
  change finiteValue (expressionValue ctrl ρ (v 0)) = n
  rw [hn]
  exact (SourceScalarCalibrationProof.natural_calibration n).1

theorem value1_of_assignment {Γ} (ctrl : Nat → Nat) (p : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary)
    (v : OrdinalVector Γ 1) (ha : assignment p a = some v) :
    value1 ctrl p ρ a = expressionValue ctrl ρ (v 1) := by
  unfold value1
  rw [ha]
  rfl

theorem project_head 
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    value1 Phi p ρ (SelectedHardness.project a b) = projectHead (value1 Phi p ρ a) (value1 Phi p ρ b) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  obtain ⟨bv,hb,hb0,hb1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ b
  rw [value1_of_assignment Phi p ρ _ _ (project_assignment p a b av bv ha hb), project_head_expression]
  change ordinalNaturalProduct ((2 : Ordinal)^(ordinalNaturalSum 1 1))
    (ordinalNaturalSum (SelectedHardness.paddedHead (expressionValue Phi ρ (av 1)))
      (expressionValue Phi ρ (bv 1))) = _
  rw [Source.SignedPair.Proof.two_power_two,ha1,hb1]
  rfl

theorem combine_head 
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    value1 Phi p ρ (SelectedHardness.combine a b) = combineHead (value1 Phi p ρ a) (value1 Phi p ρ b) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  obtain ⟨bv,hb,hb0,hb1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ b
  rw [value1_of_assignment Phi p ρ _ _ (combine_assignment p a b av bv ha hb), combine_head_expression]
  change ordinalNaturalProduct ((2 : Ordinal)^(ordinalNaturalSum 1 1))
    (ordinalNaturalSum (SelectedHardness.paddedHead (expressionValue Phi ρ (av 1)))
      (SelectedHardness.paddedHead (expressionValue Phi ρ (bv 1)))) = _
  rw [Source.SignedPair.Proof.two_power_two,ha1,hb1]
  rfl

theorem omega_head 
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ unary) :
    value1 Phi p ρ (SelectedHardness.liftOmega a) = ordinalNaturalProduct Ordinal.omega0
      (ordinalNaturalSum 1 (SelectedHardness.paddedHead (value1 Phi p ρ a))) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  rw [value1_of_assignment Phi p ρ _ _ (omega_assignment p a av ha), omega_head_expression]
  change ordinalNaturalProduct ((2 : Ordinal)^Ordinal.omega0)
    (ordinalNaturalSum 1 (SelectedHardness.paddedHead (expressionValue Phi ρ (av 1)))) = _
  have hp : (2 : Ordinal)^Ordinal.omega0 = Ordinal.omega0 := by
    simpa using Ordinal.natCast_opow_omega0 (by decide : 1 < (2 : Nat))
  rw [hp,ha1]

theorem combine_scalar 
    {Γ} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    value0 Phi p ρ (SelectedHardness.combine a b) = ParametricActualCollapse.collapseWith Phi
      (ordinalNaturalProduct Ordinal.omega0 (combineHead (value1 Phi p ρ a) (value1 Phi p ρ b)) +
      ((9*value0 Phi p ρ a+5*value0 Phi p ρ b+13 : Nat) : Ordinal)) := by
  obtain ⟨av,ha,ha0,ha1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  obtain ⟨bv,hb,hb0,hb1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ b
  apply value0_of_assignment Phi p ρ _ _ _ (combine_assignment p a b av bv ha hb)
  have hs := SelectedHardnessScalarSyntaxProof.combine_scalar_value Phi p (valuation Phi ρ) av bv
    (value0 Phi p ρ a) (value0 Phi p ρ b) ha0 hb0
  have hh : ParametricSourceSuccessor.denoteWith Phi (valuation Phi ρ) (combineHeadExpr av bv) =
      combineHead (value1 Phi p ρ a) (value1 Phi p ρ b) := by
    change ordinalNaturalProduct ((2 : Ordinal)^(ordinalNaturalSum 1 1))
      (ordinalNaturalSum (SelectedHardness.paddedHead (expressionValue Phi ρ (av 1)))
        (SelectedHardness.paddedHead (expressionValue Phi ρ (bv 1)))) = _
    rw [Source.SignedPair.Proof.two_power_two,ha1,hb1]
    rfl
  rw [hh,actualNaturalSumFiniteRight] at hs
  exact hs

end LogicLineages.PermittedControl.StandardCombinatorCoordinates.Proof
