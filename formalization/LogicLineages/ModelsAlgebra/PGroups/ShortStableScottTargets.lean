module
public import LogicLineages.ModelsAlgebra.PGroups.ShortStableScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- An actual countable stable stage below omega*gamma yields the original
unrestricted group-language Pi_(2*gamma+1) Scott upper bound. -/
def shortStableScottUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType] (α : Ordinal.{0}),
    Countable α.ToType →
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    α < Ordinal.omega0*γ → StableAt p G α →
    ∃ φ : Formula 0, Complexity .pi (2*γ+1) φ ∧
      RawScottSentence (RawGroupStructure.ofGroup G) φ
/-- Source odd-obstruction short-length upper, for an actual reduced part
of exact countable length and an arbitrary actual divisible primary part. -/
def shortReducedProductScottUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R D : Type)
    [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (γ : Ordinal.{0}) [Countable γ.ToType] (ell : Ordinal.{0}),
    Countable ell.ToType →
    (∀ x : R, ∃ k : ℕ, p^k • x = 0) →
    (∀ x : D, ∃ k : ℕ, p^k • x = 0) →
    IsReducedAddGroup R → GroupDivisible D →
    PGroupExactLength p R ell → ell < Ordinal.omega0*γ →
    ∃ φ : Formula 0, Complexity .pi (2*γ+1) φ ∧
      RawScottSentence (RawGroupStructure.ofGroup (R×D)) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
