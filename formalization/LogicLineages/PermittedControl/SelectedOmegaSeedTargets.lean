module
public import LogicLineages.PermittedControl.SelectedOmegaSeedDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedOmegaSeedTargets
open OrdinalComparison Source SelectedSourceDomain SelectedOmegaSeed
open Source.AdmissibleSum Source.SourceClasses SourceFiniteExponentProjection
open Source.FunctionalHardnessCompletion

/-- Pure collapse-free calibration includes actual grade, not a semantic supplier field. -/
def ClosedSeed : Prop := ∀ ctrl : Nat → Nat,
  exponent ctrl=ordinalNaturalSum (ordinalNaturalProduct 10 (Ordinal.omega0^2)) Ordinal.omega0 ∧
  omega ctrl=Ordinal.omega0^(ordinalNaturalSum (ordinalNaturalProduct 10 Ordinal.omega0) 1) ∧
  ClosedGrade ctrl 1 OmegaSeed.omegaExpression ∧ 0<omega ctrl ∧
  omega ctrl<epsilonZero ∧ finitePart (SignedPair.signedCNF (omega ctrl))=0

/-- Literal C2 and H2 coordinate clauses for every actual policy and admissible valuation. -/
def HigherSource : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ),
  (∃ v : OrdinalVector Γ 2,
    AdmissibleAssignment.assignment policy (@OmegaSeed.higherIdentity Γ)=some v ∧
    expressionValue ctrl ρ (v 2)=2) ∧
  (∀ a : OriginalTerm Γ OmegaSeed.higherUnary,
    ∃ av hv : OrdinalVector Γ 2,
      AdmissibleAssignment.assignment policy a=some av ∧
      AdmissibleAssignment.assignment policy (OmegaSeed.higherLift a)=some hv ∧
      expressionValue ctrl ρ (hv 2)=ordinalNaturalSum Ordinal.omega0
        (ordinalNaturalProduct (ordinalNaturalProduct 2 Ordinal.omega0)
          (expressionValue ctrl ρ (av 2)))) ∧
  (∃ v : OrdinalVector Γ 2,
    AdmissibleAssignment.assignment policy (@OmegaSeed.source Γ)=some v ∧
    expressionValue ctrl ρ (v 2)=exponent ctrl) ∧
  secondValue ctrl policy ρ (@OmegaSeed.source Γ)=exponent ctrl ∧
  InternalLevelBound 3 (@OmegaSeed.source Γ)

/-- Same actual closed source applied to both entries, no new ordinal primitive. -/
def ActualScaledPair : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ),
  InternalLevelBound 3 (@OmegaSeed.pair Γ).1 ∧ InternalLevelBound 3 (@OmegaSeed.pair Γ).2 ∧
  (∃ av bv : OrdinalVector Γ 1,
    AdmissibleAssignment.assignment policy (@OmegaSeed.pair Γ).1=some av ∧
    AdmissibleAssignment.assignment policy (@OmegaSeed.pair Γ).2=some bv ∧
    0<expressionValue ctrl ρ (av 1) ∧ 0<expressionValue ctrl ρ (bv 1)) ∧
  SelectedPairCompiler.difference ctrl policy ρ (@OmegaSeed.pair Γ)=
    (2^12 : Int) • SignedPair.signedCNF (omega ctrl)

def SelectedOmegaSeed : Prop := ClosedSeed ∧ HigherSource ∧ ActualScaledPair
end LogicLineages.PermittedControl.SelectedOmegaSeedTargets
