module
public import LogicLineages.PermittedControl.SelectedPairCompilerDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPairCompilerTargets
open OrdinalComparison Source Source.AdmissibleSum Source.SourceClasses
open SelectedSourceDomain SelectedPairCompiler

/-- Paper17 lem:pair-compiler, actual selected semantics for every policy. -/
def SemanticCompiler : Prop := ∀ (n : Nat) (d : SignedPair.Expression n),
  InternalLevelBound 2 (SignedPair.compile d).pair.1 ∧
  InternalLevelBound 2 (SignedPair.compile d).pair.2 ∧
  ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (p : Policy) (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)),
    0 < SelectedHardness.value1 ctrl p ρ (SignedPair.compile d).pair.1 ∧
    0 < SelectedHardness.value1 ctrl p ρ (SignedPair.compile d).pair.2 ∧
    difference ctrl p ρ (SignedPair.compile d).pair =
      (2^(SignedPair.compile d).exponent : Int) • SignedPair.meaning (inputs ctrl ρ) d

/-- All finite signed linear Z[omega] coefficients, including zero and negative ones. -/
def MonomialCoverage : Prop := ∀ (n : Nat) (ms : List (SignedPair.Monomial n))
    (x : Fin n → Ordinal),
  SignedPair.meaning x (SignedPair.fromMonomials ms) = SignedPair.monomialsMeaning x ms

/-- Literal expanded plain output trees and scale: no added seed or free variable. -/
def ExactOutputProgram : Prop := ∀ (n : Nat) (d : SignedPair.Expression n),
  FunctionalHardnessCompletion.SeededSourceCode.compilerCode n
      (FunctionalHardnessCompletion.SeededSourceCode.expressionCode d) =
    ((SyntaxCode.encodeTerm (SignedPair.compile d).pair.1,
      SyntaxCode.encodeTerm (SignedPair.compile d).pair.2), (SignedPair.compile d).exponent)

/-- Actual total primitive recursive program, also on malformed raw inputs. -/
def CompilerProgram : Prop :=
  Primrec₂ FunctionalHardnessCompletion.SeededSourceCode.compilerCode

def FullSelectedPairCompiler : Prop :=
  SemanticCompiler ∧ MonomialCoverage ∧ ExactOutputProgram ∧ CompilerProgram
end LogicLineages.PermittedControl.SelectedPairCompilerTargets
