module
public import LogicLineages.PermittedControl.SelectedPolynomialPatternsDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialPatternsTargets
open OrdinalComparison Source SelectedSourceDomain SelectedSystemReduction SelectedPolynomialPatterns
open Source.AdmissibleSum SourcePolynomialRealization SourceFiniteExponentProjection
open Source.FunctionalHardnessCompletion (System PolynomialSolves PolynomialSatisfiable masks restrictSystem)

def ProjectionCalibration : Prop :=
  (∀ (a : Ordinal) (n : Nat), 0≤finitePart (SignedPair.signedCNF a) n) ∧
  (∀ a : Ordinal, signedCoefficients (projectedPolynomial a)=finitePart (SignedPair.signedCNF a)) ∧
  (∀ (n : Nat) (x : Fin n → Ordinal) (d : SignedPair.Expression n),
    polynomialMeaning (fun i => signedCoefficients (projectedPolynomial (x i))) d=
      finitePart (SignedPair.meaning x d))

def SharedPolynomialLift : Prop := ∀ (ctrl : Nat → Nat) (n : Nat) (s : System n)
    (p : Fin n → NonnegativePolynomial), (∀ i, p i≠0) → PolynomialSolves s p →
  ∃ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n), OrdinalSolves ctrl s ρ

def ActualProjection : Prop := ∀ (ctrl : Nat → Nat) (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)), OrdinalSolves ctrl s ρ →
  PolynomialSolves s (fun i => projectedPolynomial (SelectedPairCompiler.inputs ctrl ρ i))

def SimultaneousPatterns : Prop := ∀ (ctrl : Nat → Nat) (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔ ∃ z ∈ masks n,
    ∃ ρ : AdmissibleSubstitution ctrl (SignedPair.Context n), OrdinalSolves ctrl (restrictSystem z s) ρ

def AllMaskQueries : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (policy : Policy) (n : Nat) (s : System n),
  (¬PolynomialSatisfiable s ↔ ∀ z ∈ masks n, universalStrictSystem ctrl policy (restrictSystem z s)) ∧
  (¬PolynomialSatisfiable s ↔ ∀ z ∈ masks n, universalWeakSystem ctrl policy (restrictSystem z s))

def SelectedPolynomialPatterns : Prop := ProjectionCalibration ∧ SharedPolynomialLift ∧
  ActualProjection ∧ SimultaneousPatterns ∧ AllMaskQueries
end LogicLineages.PermittedControl.SelectedPolynomialPatternsTargets
