module
public import LogicLineages.OrdinalComparison.SourceSignedPairDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair.Targets
open OriginalDomain SourceClasses

/-- Whole original hardness.tex lem:pair-compiler. The compiler is executable,
its output is actual source syntax, and all valuations are the genuine original
admissible substitutions (no finite-head restriction). Both positive coordinates
remain positive ordinals. The equality is only in the signed Cantor group. -/
def SignedPairCompiler : Prop :=
  ∀ (n : Nat) (d : Expression n),
    InternalLevelBound 2 (compile d).pair.1 ∧
    InternalLevelBound 2 (compile d).pair.2 ∧
    ∀ ρ : AdmissibleSubstitution (Context n),
      0 < FunctionalDetector.Proof.value1 ρ (compile d).pair.1 ∧
      0 < FunctionalDetector.Proof.value1 ρ (compile d).pair.2 ∧
      difference ρ (compile d).pair = (2^(compile d).exponent : Int) • meaning (inputs ρ) d

/-- Every finite list of signed linear Z[omega] monomials is accepted, including
zero and negative coefficients, arbitrary finite powers, and a constant term. -/
def MonomialAdapter : Prop :=
  ∀ (n : Nat) (ms : List (Monomial n)) (x : Fin n → Ordinal),
    meaning x (fromMonomials ms) = monomialsMeaning x ms
end LogicLineages.OrdinalComparison.Source.SignedPair.Targets
