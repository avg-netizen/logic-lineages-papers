module
public import LogicLineages.ModelsAlgebra.PGroups.TupleOrbitDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Actual lower difference Scott sentence, paying the source short-length
pure-Sigma exclusion without assuming a general Miller/orbit theorem. -/
def shortStableSigmaScottLowering : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType] (α:Ordinal.{0}),
    0<γ → Countable α.ToType →
    (∀x:G,∃k:ℕ,p^k • x=0) → α<Ordinal.omega0*γ → StableAt p G α →
    ∀φ:Formula 0, Complexity .sigma (2*γ+1) φ → GroupScottSentence G φ →
      ∃d:DifferenceFormula 0, d.AtLevel (2*γ) ∧ DifferenceScottSentence G d
/-- Same literal source lowering in unrestricted raw-model Scott semantics. -/
def shortStableRawSigmaScottLowering : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType] (α:Ordinal.{0}),
    0<γ → Countable α.ToType →
    (∀x:G,∃k:ℕ,p^k • x=0) → α<Ordinal.omega0*γ → StableAt p G α →
    ∀φ:Formula 0, Complexity .sigma (2*γ+1) φ →
      RawScottSentence (RawGroupStructure.ofGroup G) φ →
      ∃d:DifferenceFormula 0, d.AtLevel (2*γ) ∧
        RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
end LogicLineages.ModelsAlgebra.PGroups.Targets
