module
public import LogicLineages.ModelsAlgebra.PGroups.NoPureSigmaDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Remaining positive-gamma even source case, on arbitrary countable
primary groups including their actual divisible part. -/
def primaryEvenSigmaLowering : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType],
    (∀x:G,∃k:ℕ,p^k • x=0) → 0<γ →
    ∀φ:Formula 0,Complexity .sigma (2*γ+2) φ →
      RawScottSentence (RawGroupStructure.ofGroup G) φ →
      ((∃ψ:Formula 0,Complexity .pi (2*γ+1) ψ ∧ RawScottSentence (RawGroupStructure.ofGroup G) ψ) ∨
        ∃d:DifferenceFormula 0,d.AtLevel (2*γ+1) ∧ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d)
/-- Entire original thm:no-pure-sigma, witnessed more strongly by an actual
strictly lower-index Scott description for EVERY putative countable-index
raw Sigma Scott sentence. All primary groups, all countable ordinals,
zero, one, limit, odd and even indices are quantified literally. -/
def primaryAllSigmaLowering : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (α:Ordinal.{0}) [Countable α.ToType],
    (∀x:G,∃k:ℕ,p^k • x=0) →
    ∀φ:Formula 0,Complexity .sigma α φ →
      RawScottSentence (RawGroupStructure.ofGroup G) φ → LowerRawScottDescription G α
end LogicLineages.ModelsAlgebra.PGroups.Targets
