module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaSeedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed.Targets
open OriginalDomain SourceFiniteExponentProjection SourceClasses

def ExactClosedSeed : Prop :=
  exponent = ordinalNaturalSum (ordinalNaturalProduct 10 (Ordinal.omega0^2)) Ordinal.omega0 ∧
  omega = Ordinal.omega0^(ordinalNaturalSum (ordinalNaturalProduct 10 Ordinal.omega0) 1) ∧
  ClosedGrade 1 omegaExpression ∧ 0 < omega ∧ finitePart (SignedPair.signedCNF omega) = 0

def ActualHigherSource : Prop := ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ),
  secondValue ρ source = exponent ∧ InternalLevelBound 3 (@source Γ)

def ActualScaledPair : Prop := ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ),
  InternalLevelBound 3 (@pair Γ).1 ∧ InternalLevelBound 3 (@pair Γ).2 ∧
  SignedPair.difference ρ pair = (2^12 : Int) • SignedPair.signedCNF omega

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed.Targets
