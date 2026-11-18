module
public import LogicLineages.PermittedControl.SelectedOmegaSyntaxProof
public import LogicLineages.PermittedControl.SelectedOmegaAlgebraProof
public import LogicLineages.PermittedControl.SelectedCanonicalDomainProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
open OrdinalComparison Source SelectedSourceDomain
open Source.AdmissibleSum Source.AdmissibleAssignment
open Source.FunctionalDetector (unary)
open Source.FunctionalHardnessCompletion

 theorem source_assignment (policy : Policy) (Γ : List Ty) :
    assignment policy (@OmegaSeed.source Γ)=some (higherVector policy (higherVector policy (identityVector policy Γ))) :=
  higher_assignment policy _ _ (higher_assignment policy _ _ (identity_assignment policy Γ))

 theorem source_coordinate (ctrl : Nat → Nat) (policy : Policy) {Γ}
    (ρ : AdmissibleSubstitution ctrl Γ) :
    expressionValue ctrl ρ (higherVector policy (higherVector policy (identityVector policy Γ)) 2)=
      exponent ctrl := by
  simp [higher_head_expression,identityVector,exponent,OmegaSeed.exponentExpression,OmegaSeed.topStep,
    expressionValue,closedValue,ParametricSourceSuccessor.denoteWith]

 theorem source_second (ctrl : Nat → Nat) (policy : Policy) {Γ}
    (ρ : AdmissibleSubstitution ctrl Γ) : secondValue ctrl policy ρ (@OmegaSeed.source Γ)=exponent ctrl := by
  unfold secondValue
  rw [source_assignment]
  exact source_coordinate ctrl policy ρ

 theorem higherSource : SelectedOmegaSeedTargets.HigherSource := by
  intro ctrl K hc Γ policy ρ
  refine ⟨?_,?_,?_,source_second ctrl policy ρ,OmegaSeed.Proof.source_bound Γ⟩
  · refine ⟨identityVector policy Γ,identity_assignment policy Γ,?_⟩
    change ordinalNaturalSum 1 1=2
    simpa using LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof.naturalSum_finite 1 1
  · intro a
    obtain ⟨av,ha,_⟩ := SelectedCanonicalDomainProof.canonicalAssignment ctrl K hc Γ OmegaSeed.higherUnary policy a
    refine ⟨av,higherVector policy av,ha,higher_assignment policy a av ha,?_⟩
    rw [higher_head_expression]
    change ordinalNaturalProduct ((2 : Ordinal)^Ordinal.omega0)
      (ordinalNaturalSum 1 (ordinalNaturalSum (expressionValue ctrl ρ (av 2)) (expressionValue ctrl ρ (av 2))))=_
    exact higher_value _ (SelectedValueClosureProof.ambient_below ctrl ρ (av 2))
  · exact ⟨_,source_assignment policy Γ,source_coordinate ctrl policy ρ⟩
end LogicLineages.PermittedControl.SelectedOmegaSeed.Proof
