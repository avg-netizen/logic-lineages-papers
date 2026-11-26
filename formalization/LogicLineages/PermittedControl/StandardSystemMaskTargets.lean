module
public import LogicLineages.PermittedControl.SelectedSystemReductionDefinitions
public import LogicLineages.PermittedControl.SelectedPolynomialPatternsDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSystemMask
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector SelectedSystemReduction SelectedPolynomialPatterns
open Source.AdmissibleSum SourcePolynomialRealization SourceFiniteExponentProjection
open Source.FunctionalHardnessCompletion (System compileSystem strictSystemPair weakSystemPair PolynomialSolves PolynomialSatisfiable masks restrictSystem)

/-- Actual arbitrary-control expression transport, including every old coordinate. -/
def ActualRenaming : Prop := ∀ (Γ Δ : List Ty) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution Phi Γ) (σ : AdmissibleSubstitution Phi Δ),
  Preserves Phi r ρ σ →
  (∀ t : OrdinalExpression Γ,
    expressionValue Phi σ (ordinalExpressionRename r t)=expressionValue Phi ρ t) ∧
  (∀ (policy : Policy) (t : OriginalTerm Γ .ground),
    groundValue Phi policy σ (t.rename r)=groundValue Phi policy ρ t)

/-- The same original valuation is retained simultaneously in all compiled equations. -/
def ValuationPreservingSystem : Prop := ∀ (policy : Policy) (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution Phi (SignedPair.Context n)),
  OrdinalSolves Phi s ρ ↔ ∃ σ : AdmissibleSubstitution Phi (compileSystem s).context,
    Preserves Phi (compileSystem s).original ρ σ ∧
    SelectedAggregation.AllEqual Phi policy σ (compileSystem s).detectors

def SystemEquality : Prop := ∀ (policy : Policy) (n : Nat) (s : System n),
  (∃ ρ : AdmissibleSubstitution Phi (SignedPair.Context n), OrdinalSolves Phi s ρ) ↔
  ∃ σ : AdmissibleSubstitution Phi (compileSystem s).context,
    groundValue Phi policy σ (strictSystemPair s).1=groundValue Phi policy σ (strictSystemPair s).2

def QueryComplements : Prop := ∀ (policy : Policy) (n : Nat) (s : System n),
  (universalStrictSystem Phi policy s ↔
    ¬∃ ρ : AdmissibleSubstitution Phi (SignedPair.Context n), OrdinalSolves Phi s ρ) ∧
  (universalWeakSystem Phi policy s ↔
    ¬∃ ρ : AdmissibleSubstitution Phi (SignedPair.Context n), OrdinalSolves Phi s ρ)

def LevelTwoBounds : Prop := ∀ (n : Nat) (s : System n),
  (∀ τ ∈ (compileSystem s).context, τ.level≤1) ∧
  SourceClasses.InternalLevelBound 2 (strictSystemPair s).1 ∧
  SourceClasses.InternalLevelBound 2 (strictSystemPair s).2 ∧
  SourceClasses.InternalLevelBound 2 (weakSystemPair s).1 ∧
  SourceClasses.InternalLevelBound 2 (weakSystemPair s).2

def ProjectionCalibration : Prop :=
  (∀ (a : Ordinal) (n : Nat), 0≤finitePart (SignedPair.signedCNF a) n) ∧
  (∀ a : Ordinal, signedCoefficients (projectedPolynomial a)=finitePart (SignedPair.signedCNF a)) ∧
  (∀ (n : Nat) (x : Fin n → Ordinal) (d : SignedPair.Expression n),
    polynomialMeaning (fun i => signedCoefficients (projectedPolynomial (x i))) d=
      finitePart (SignedPair.meaning x d))

def SharedPolynomialLift : Prop := ∀ (n : Nat) (s : System n)
    (p : Fin n → NonnegativePolynomial), (∀ i, p i≠0) → PolynomialSolves s p →
  ∃ ρ : AdmissibleSubstitution Phi (SignedPair.Context n), OrdinalSolves Phi s ρ

def ActualProjection : Prop := ∀ (n : Nat) (s : System n)
    (ρ : AdmissibleSubstitution Phi (SignedPair.Context n)), OrdinalSolves Phi s ρ →
  PolynomialSolves s (fun i => projectedPolynomial (SelectedPairCompiler.inputs Phi ρ i))

def SimultaneousPatterns : Prop := ∀ (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔ ∃ z ∈ masks n,
    ∃ ρ : AdmissibleSubstitution Phi (SignedPair.Context n), OrdinalSolves Phi (restrictSystem z s) ρ

def AllMaskQueries : Prop := ∀ (policy : Policy) (n : Nat) (s : System n),
  (¬PolynomialSatisfiable s ↔ ∀ z ∈ masks n, universalStrictSystem Phi policy (restrictSystem z s)) ∧
  (¬PolynomialSatisfiable s ↔ ∀ z ∈ masks n, universalWeakSystem Phi policy (restrictSystem z s))

def StandardSystemMask : Prop := ActualRenaming ∧ ValuationPreservingSystem ∧
  SystemEquality ∧ QueryComplements ∧ LevelTwoBounds ∧ ProjectionCalibration ∧
  SharedPolynomialLift ∧ ActualProjection ∧ SimultaneousPatterns ∧ AllMaskQueries
end LogicLineages.PermittedControl.StandardSystemMask
