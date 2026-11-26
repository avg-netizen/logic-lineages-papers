module
public import LogicLineages.PermittedControl.SelectedSeededCompilerDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSeededCompiler
open OrdinalComparison Source Source.SignedPair Source.AdmissibleSum SelectedSourceDomain
open Source.FunctionalHardnessCompletion SourcePolynomialRealization

/-- Actual unchanged Phi, same original context, one closed source seed, every genuine policy. -/
def ActualCompiler : Prop := ∀ (n : Nat) (d : Expression (n+1)),
  SourceClasses.InternalLevelBound 3 (SeededCompiler.compile d).pair.1 ∧
  SourceClasses.InternalLevelBound 3 (SeededCompiler.compile d).pair.2 ∧
  ∀ (policy : Policy) (ρ : AdmissibleSubstitution Phi (Context n)),
  (∃ av bv : OrdinalVector (Context n) 1,
    AdmissibleAssignment.assignment policy (SeededCompiler.compile d).pair.1=some av ∧
    AdmissibleAssignment.assignment policy (SeededCompiler.compile d).pair.2=some bv ∧
    0 < expressionValue Phi ρ (av 1) ∧ 0 < expressionValue Phi ρ (bv 1)) ∧
  SelectedPairCompiler.difference Phi policy ρ (SeededCompiler.compile d).pair=
    (2^(SeededCompiler.compile d).exponent : Int) •
      meaning (SelectedSeededCompiler.seededInputs Phi ρ) d

def SeedSubstitution : Prop := ∀ (n : Nat) (x : Fin n → Ordinal) (seed : Ordinal)
    (d : Expression n),
  meaning (Fin.lastCases seed x) (SeededCompiler.subtractSeed d)=
    SeededCompiler.linearMeaning (fun i => signedCNF (x i)-signedCNF seed) d

/-- Shared actual admissible realization includes zero polynomial unknowns. -/
def SharedSeededFamily : Prop := ∀ (n : Nat) (p : Fin n → NonnegativePolynomial),
  ∃ ρ : AdmissibleSubstitution Phi (Context n), ∀ i,
    signedCNF (SelectedPairCompiler.inputs Phi ρ i)=
      embeddedCoefficients (p i)+signedCNF (SelectedOmegaSeed.omega Phi)

/-- No mask, extra original variable, or bound on the admitted source valuation. -/
def SimultaneousSolvability : Prop := ∀ (n : Nat) (s : System n),
    PolynomialSatisfiable s ↔ SelectedSeededCompiler.OrdinalSatisfiable Phi s

def StandardSeededCompiler : Prop := ActualCompiler ∧ SeedSubstitution ∧
  SharedSeededFamily ∧ SimultaneousSolvability
end LogicLineages.PermittedControl.StandardSeededCompiler
