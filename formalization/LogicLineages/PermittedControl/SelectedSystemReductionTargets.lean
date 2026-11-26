module
public import LogicLineages.PermittedControl.SelectedSystemReductionDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSystemReductionTargets
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector SelectedSystemReduction
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion (System compileSystem strictSystemPair weakSystemPair)

/-- Actual arbitrary-control expression transport, including every old coordinate. -/
def ActualRenaming : Prop := ∀ (ctrl : Nat → Nat) (Γ Δ : List Ty) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution ctrl Γ) (σ : AdmissibleSubstitution ctrl Δ),
  Preserves ctrl r ρ σ →
  (∀ t : OrdinalExpression Γ,
    expressionValue ctrl σ (ordinalExpressionRename r t)=expressionValue ctrl ρ t) ∧
  (∀ (policy : Policy) (t : OriginalTerm Γ .ground),
    groundValue ctrl policy σ (t.rename r)=groundValue ctrl policy ρ t)

/-- The same original valuation is retained simultaneously in all compiled equations. -/
def ValuationPreservingSystem : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)),
  OrdinalSolves ctrl s ρ ↔ ∃ σ : AdmissibleSubstitution ctrl (compileSystem s).context,
    Preserves ctrl (compileSystem s).original ρ σ ∧
    SelectedAggregation.AllEqual ctrl policy σ (compileSystem s).detectors

def SystemEquality : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n),
  (∃ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n), OrdinalSolves ctrl s ρ) ↔
  ∃ σ : AdmissibleSubstitution ctrl (compileSystem s).context,
    groundValue ctrl policy σ (strictSystemPair s).1=groundValue ctrl policy σ (strictSystemPair s).2

def QueryComplements : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n),
  (universalStrictSystem ctrl policy s ↔
    ¬∃ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n), OrdinalSolves ctrl s ρ) ∧
  (universalWeakSystem ctrl policy s ↔
    ¬∃ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n), OrdinalSolves ctrl s ρ)

def LevelTwoBounds : Prop := ∀ (n : Nat) (s : System n),
  (∀ τ ∈ (compileSystem s).context, τ.level≤1) ∧
  SourceClasses.InternalLevelBound 2 (strictSystemPair s).1 ∧
  SourceClasses.InternalLevelBound 2 (strictSystemPair s).2 ∧
  SourceClasses.InternalLevelBound 2 (weakSystemPair s).1 ∧
  SourceClasses.InternalLevelBound 2 (weakSystemPair s).2

def SelectedSystemReduction : Prop := ActualRenaming ∧ ValuationPreservingSystem ∧
  SystemEquality ∧ QueryComplements ∧ LevelTwoBounds
end LogicLineages.PermittedControl.SelectedSystemReductionTargets
