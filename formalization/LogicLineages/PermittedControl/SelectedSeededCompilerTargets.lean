module
public import LogicLineages.PermittedControl.SelectedSeededCompilerDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededCompilerTargets
open OrdinalComparison Source Source.SignedPair Source.AdmissibleSum SelectedSourceDomain
open Source.FunctionalHardnessCompletion SourcePolynomialRealization

/-- Same original context, one closed seed branch, every genuine policy. -/
def ActualCompiler : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (n : Nat) (d : Expression (n+1)),
  SourceClasses.InternalLevelBound 3 (SeededCompiler.compile d).pair.1 ∧
  SourceClasses.InternalLevelBound 3 (SeededCompiler.compile d).pair.2 ∧
  ∀ (policy : Policy) (ρ : AdmissibleSubstitution ctrl (Context n)),
  (∃ av bv : OrdinalVector (Context n) 1,
    AdmissibleAssignment.assignment policy (SeededCompiler.compile d).pair.1=some av ∧
    AdmissibleAssignment.assignment policy (SeededCompiler.compile d).pair.2=some bv ∧
    0 < expressionValue ctrl ρ (av 1) ∧ 0 < expressionValue ctrl ρ (bv 1)) ∧
  SelectedPairCompiler.difference ctrl policy ρ (SeededCompiler.compile d).pair=
    (2^(SeededCompiler.compile d).exponent : Int) •
      meaning (SelectedSeededCompiler.seededInputs ctrl ρ) d

def SeedSubstitution : Prop := ∀ (n : Nat) (x : Fin n → Ordinal) (seed : Ordinal)
    (d : Expression n),
  meaning (Fin.lastCases seed x) (SeededCompiler.subtractSeed d)=
    SeededCompiler.linearMeaning (fun i => signedCNF (x i)-signedCNF seed) d

/-- Shared actual admissible realization includes zero polynomial unknowns. -/
def SharedSeededFamily : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (n : Nat) (p : Fin n → NonnegativePolynomial),
  ∃ ρ : AdmissibleSubstitution ctrl (Context n), ∀ i,
    signedCNF (SelectedPairCompiler.inputs ctrl ρ i)=
      embeddedCoefficients (p i)+signedCNF (SelectedOmegaSeed.omega ctrl)

/-- No mask, extra original variable, or bound on the admitted source valuation. -/
def SimultaneousSolvability : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ (n : Nat) (s : System n),
    PolynomialSatisfiable s ↔ SelectedSeededCompiler.OrdinalSatisfiable ctrl s

def SelectedSeededCompiler : Prop := ActualCompiler ∧ SeedSubstitution ∧
  SharedSeededFamily ∧ SimultaneousSolvability
end LogicLineages.PermittedControl.SelectedSeededCompilerTargets
