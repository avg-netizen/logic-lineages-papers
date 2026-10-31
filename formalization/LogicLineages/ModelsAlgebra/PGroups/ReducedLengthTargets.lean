module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def countableReducedExactLength : Prop :=
  ∀ (G:Type) [AddCommGroup G] [Countable G] (p:ℕ) [Fact p.Prime],
    (∀x:G,∃k:ℕ,p^k • x=0) → IsReducedAddGroup G →
    ∃! ell:Ordinal.{0}, Countable ell.ToType ∧ PGroupExactLength p G ell
def countableLengthNormalForm : Prop :=
  ∀ ell:Ordinal.{0}, Countable ell.ToType →
    ∃! z:Ordinal.{0}×ℕ, Countable z.1.ToType ∧ ell=Ordinal.omega0*z.1+z.2
def exactLengthTerminalBound : Prop :=
  ∀ (G:Type) [AddCommGroup G] (p:ℕ) (γ:Ordinal.{0}) (n:ℕ),
    PGroupExactLength p G (Ordinal.omega0*γ+n) →
    (∀x:(transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G), p^n • x=0) ∧
    (0<n → ∃x:(transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G), p^(n-1) • x≠0)
end LogicLineages.ModelsAlgebra.PGroups.Targets
