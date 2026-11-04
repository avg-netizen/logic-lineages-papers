module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Targets
open OriginalDomain SignedPair

/-- Actual typed source values and internal level THREE, for arbitrary genuine
admissible substitutions in the unchanged original unary-variable context. -/
def ExactSeededCompiler : Prop := ∀ (n : Nat) (d : Expression (n+1)),
  SourceClasses.InternalLevelBound 3 (compile d).pair.1 ∧
  SourceClasses.InternalLevelBound 3 (compile d).pair.2 ∧
  ∀ ρ : AdmissibleSubstitution (Context n),
    difference ρ (compile d).pair =
      (2^(compile d).exponent : Int) • meaning (seededInputs ρ) d

/-- This syntactic substitution retains the entire shared valuation. -/
def ExactSeedSubstitution : Prop := ∀ (n : Nat) (x : Fin n → Ordinal) (seed : Ordinal)
    (d : Expression n),
  meaning (Fin.lastCases seed x) (subtractSeed d) =
    linearMeaning (fun i => signedCNF (x i)-signedCNF seed) d

/-- Both directions hold for a simultaneous system, including an empty system,
zero unknowns, and zero-valued polynomial unknowns. The RHS is ONE source
valuation with a fixed closed seed, never an existential mask. -/
def ExactSeededSatisfiability : Prop := ∀ (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔ OrdinalSatisfiable s

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Targets
