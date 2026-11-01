module
public import LogicLineages.ModelsAlgebra.PGroups.PointedTableDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.TupleOrbitDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RelativizedDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth GroupInfinitary
/-- Actual Sigma1 embeddings with prescribed term values, in every group. -/
def pointedFiniteTableCorrect : Prop :=
  ∀ (K:Type) [AddCommGroup K] [Fintype K] (n m:ℕ)
    (a:Fin m→K) (t:Fin m→GroupTerm n),
    Complexity .sigma (1:Ordinal.{0}) (pointedTableFormula K n m a t) ∧
    ∀ (G:Type) [AddCommGroup G] (b:Fin n→G),
      (pointedTableFormula K n m a t).Realize b ↔
        ∃f:K→+G, Function.Injective f ∧ ∀i, f (a i)=(t i).eval b
/-- Exact quantifier relativization keeps free term parameters ambient and
requires the actual finite table embedding into the actual chosen subgroup. -/
def pointedFiniteTableRelativeCorrect : Prop :=
  ∀ (K:Type) [AddCommGroup K] [Fintype K] (n m:ℕ)
    (a:Fin m→K) (t:Fin m→GroupTerm n),
    ∀ (G:Type) [AddCommGroup G] (S:AddSubgroup G) (b:Fin n→G),
      (pointedTableFormula K n m a t).RealizeIn S b ↔
        ∃f:K→+S, Function.Injective f ∧ ∀i, (f (a i):G)=(t i).eval b
/-- Every tuple of any actual countable primary group with finite socle
has a literal original-language Sigma1 orbit formula. -/
def finiteSocleSigmaOneOrbits : Prop :=
  ∀ (G:Type) [AddCommGroup G] [Countable G] (p:ℕ) [Fact p.Prime]
    [Finite (pSocle p (⊤:AddSubgroup G))],
    (∀x:G,∃k:ℕ,p^k • x=0) → ∀ (n:ℕ) (a:Fin n→G),
      ∃φ:Formula n, Complexity .sigma (1:Ordinal.{0}) φ ∧
        ∀b:Fin n→G, φ.Realize b ↔ TupleOrbit a b
end LogicLineages.ModelsAlgebra.PGroups.Targets
