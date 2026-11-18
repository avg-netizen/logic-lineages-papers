module
public import LogicLineages.PermittedControl.SelectedPairCompilerDefinitions
public import LogicLineages.PermittedControl.StandardCombinatorCoordinatesTargets
@[expose] public section
namespace LogicLineages.PermittedControl.StandardPairCompiler
open OrdinalComparison Source Source.AdmissibleSum Source.SourceClasses
open SelectedSourceDomain SelectedPairCompiler

/-- Actual shared original n-variable context, all policies, genuine calibrated outputs. -/
def SemanticCompiler : Prop := ∀ (n : Nat) (d : SignedPair.Expression n),
  InternalLevelBound 2 (SignedPair.compile d).pair.1 ∧
  InternalLevelBound 2 (SignedPair.compile d).pair.2 ∧
  ∀ (p : Policy) (ρ : AdmissibleSubstitution Phi (SignedPair.Context n)),
    StandardCombinatorCoordinates.UnaryOutput p ρ (SignedPair.compile d).pair.1 ∧
    StandardCombinatorCoordinates.UnaryOutput p ρ (SignedPair.compile d).pair.2 ∧
    difference Phi p ρ (SignedPair.compile d).pair =
      (2^(SignedPair.compile d).exponent : Int) • SignedPair.meaning (inputs Phi ρ) d

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

def StandardPairCompiler : Prop :=
  SemanticCompiler ∧ MonomialCoverage ∧ ExactOutputProgram ∧ CompilerProgram
end LogicLineages.PermittedControl.StandardPairCompiler
