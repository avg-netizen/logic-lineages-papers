module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCompetitorDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth
/-- The infinite-socle side is the CODOMAIN of f, hence the LEFT side of
the actual asymmetric comparison. Domain socles only need the R reservoir
below the omega cut; no infinite-rank hypothesis is placed on D. -/
def infiniteSocleOddProductComparison : Prop :=
  ∀ (R D E:Type) [AddCommGroup R] [AddCommGroup D] [AddCommGroup E]
    [Countable R] [Countable D] [Countable E] (p:ℕ) [Fact p.Prime]
    [Infinite (pSocle p (⊤:AddSubgroup E))],
    (∀x:R,∃k:ℕ,p^k • x=0) → (∀x:D,∃k:ℕ,p^k • x=0) →
    (∀x:E,∃k:ℕ,p^k • x=0) → IsReducedAddGroup R →
    GroupDivisible D → GroupDivisible E →
    ∀γ:Ordinal.{0}, StagesNonzeroBelow p R (Ordinal.omega0*γ) →
    ∀ (B:AddSubgroup (R×D)) (C:AddSubgroup (R×E)) [Finite B] (f:B≃+C),
      (∀x:B,(f x:R×E).1=(x:R×D).1) → SubgroupComparison f (2*γ+1)
/-- An actual finite-divisible-image competitor at the stronger pointed odd
rank; nonisomorphism, finite image and BF comparison are all conclusions. -/
def infiniteSocleOddProductCompetitor : Prop :=
  ∀ (R D:Type) [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p:ℕ) [Fact p.Prime] [Infinite (pSocle p (⊤:AddSubgroup D))],
    (∀x:R,∃k:ℕ,p^k • x=0) → (∀x:D,∃k:ℕ,p^k • x=0) →
    IsReducedAddGroup R → GroupDivisible D →
    ∀γ:Ordinal.{0}, StagesNonzeroBelow p R (Ordinal.omega0*γ) →
    ∀ (n:ℕ) (a:Fin n→R×D),
      ∃ (H:Type) (inst:AddCommGroup H), letI:=inst; Countable H ∧
        (∀x:H,∃k:ℕ,p^k • x=0) ∧ ¬Nonempty ((R×D)≃+H) ∧
        ∃b:Fin n→H, BackAndForth (2*γ+1) a b
/-- The source even-form infinite-divisible case, without a prescribed-tail
realization premise. Gamma0 and all countable positive gamma are included. -/
def infiniteSocleNoEvenRawSigma : Prop :=
  ∀ (R D:Type) [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p:ℕ) [Fact p.Prime] [Infinite (pSocle p (⊤:AddSubgroup D))],
    (∀x:R,∃k:ℕ,p^k • x=0) → (∀x:D,∃k:ℕ,p^k • x=0) →
    IsReducedAddGroup R → GroupDivisible D →
    ∀γ:Ordinal.{0}, Countable γ.ToType → StagesNonzeroBelow p R (Ordinal.omega0*γ) →
    ∀φ:Formula 0, Complexity .sigma (2*γ+2) φ →
      ¬RawScottSentence (RawGroupStructure.ofGroup (R×D)) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
