module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCompetitorDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth GroupInfinitary
/-- Actual bounded infinite reduced tail, unchanged finite-rank divisible
part, and an actual pointed nonisomorphic competitor at the odd matrix rank. -/
def boundedReducedProductCompetitor : Prop :=
  ∀ (R D:Type) [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p:ℕ) [Fact p.Prime] [Finite (pSocle p (⊤:AddSubgroup D))],
    (∀x:R,∃k:ℕ,p^k • x=0) → (∀x:D,∃k:ℕ,p^k • x=0) →
    IsReducedAddGroup R → GroupDivisible D →
    ∀ (γ:Ordinal.{0}) (N:ℕ),
    (∀x:(transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup R),p^N • x=0) →
    Infinite (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup R) →
    ∀ (n:ℕ) (a:Fin n→R×D),
      ∃ (H:Type) (inst:AddCommGroup H), letI:=inst; Countable H ∧
        (∀x:H,∃k:ℕ,p^k • x=0) ∧ ¬Nonempty ((R×D)≃+H) ∧
        ∃b:Fin n→H,BackAndForth (2*γ+1) a b
/-- Source no-pure-Sigma infinite bounded reduced-tail case with an
unchanged actual finite-socle divisible summand. -/
def boundedReducedProductNoEvenRawSigma : Prop :=
  ∀ (R D:Type) [AddCommGroup R] [AddCommGroup D] [Countable R] [Countable D]
    (p:ℕ) [Fact p.Prime] [Finite (pSocle p (⊤:AddSubgroup D))],
    (∀x:R,∃k:ℕ,p^k • x=0) → (∀x:D,∃k:ℕ,p^k • x=0) →
    IsReducedAddGroup R → GroupDivisible D →
    ∀ (γ:Ordinal.{0}) (N:ℕ),
    (∀x:(transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup R),p^N • x=0) →
    Infinite (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup R) →
    ∀φ:Formula 0,Complexity .sigma (2*γ+2) φ →
      ¬RawScottSentence (RawGroupStructure.ofGroup (R×D)) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
