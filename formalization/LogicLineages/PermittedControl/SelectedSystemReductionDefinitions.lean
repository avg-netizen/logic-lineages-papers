module
public import LogicLineages.PermittedControl.SelectedAggregationDefinitions
public import LogicLineages.PermittedControl.SelectedPairCompilerDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemSourceDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSystemReduction
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open Source.FunctionalHardnessCompletion (System compileSystem strictSystemPair weakSystemPair)

def pullback {Γ Δ : List Ty} (ctrl : Nat → Nat) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution ctrl Δ) : AdmissibleSubstitution ctrl Γ where
  vector := fun {_} x j => ρ.vector (r x) j
  graded := fun x j => ρ.graded (r x) j
  bounded := fun x j => ρ.bounded (r x) j

def Preserves {Γ Δ : List Ty} (ctrl : Nat → Nat) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution ctrl Γ) (σ : AdmissibleSubstitution ctrl Δ) : Prop :=
  ∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)), σ.vector (r x) j=ρ.vector x j

def OrdinalSolves {n : Nat} (ctrl : Nat → Nat) (s : System n)
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)) : Prop :=
  ∀ d ∈ s, SignedPair.meaning (SelectedPairCompiler.inputs ctrl ρ) d=0

def universalStrictSystem {n : Nat} (ctrl : Nat → Nat) (policy : Policy) (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution ctrl (compileSystem s).context,
    groundValue ctrl policy ρ (strictSystemPair s).2<groundValue ctrl policy ρ (strictSystemPair s).1

def universalWeakSystem {n : Nat} (ctrl : Nat → Nat) (policy : Policy) (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution ctrl (compileSystem s).context,
    groundValue ctrl policy ρ (weakSystemPair s).1≤groundValue ctrl policy ρ (weakSystemPair s).2
end LogicLineages.PermittedControl.SelectedSystemReduction
