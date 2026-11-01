module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleOddSigmaDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Source first assertion with the actual reduced length, not an abstract
comparison/rank supplier or an externally provided decomposition theorem. -/
def oddLongSourceNoSigma : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (R D:Type) [AddCommGroup R] [AddCommGroup D]
    [Countable R] [Countable D] (γ:Ordinal.{0}) [Countable γ.ToType] (ell:Ordinal.{0}),
    (∀x:R,∃k:ℕ,p^k • x=0) → (∀x:D,∃k:ℕ,p^k • x=0) →
    IsReducedAddGroup R → GroupDivisible D → 0<γ →
    PGroupExactLength p R ell → Ordinal.omega0*γ≤ell →
    ∀φ:Formula 0, Complexity .sigma (2*γ+1) φ →
      ¬RawScottSentence (RawGroupStructure.ofGroup (R×D)) φ
/-- A stronger explicit witness for the source no-exact-pure clause:
every putative odd Sigma Scott description of ANY countable primary group
has a genuinely lower raw difference Scott description. Exactness is not
redefined to mean lack of a same-level Pi description. -/
def oddPrimarySigmaLowering : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType],
    (∀x:G,∃k:ℕ,p^k • x=0) → 0<γ →
    ∀φ:Formula 0, Complexity .sigma (2*γ+1) φ →
      RawScottSentence (RawGroupStructure.ofGroup G) φ →
      ∃d:DifferenceFormula 0, d.AtLevel (2*γ) ∧
        RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
/-- Whole paper01 thm:odd-obstruction, both original clauses. The explicit
lower-description witness has rank2*gamma<2*gamma+1, so rules out exact
pure Sigma without assuming Miller or merely redefining its conclusion. -/
def oddObstructionFullSource : Prop := oddLongSourceNoSigma ∧ oddPrimarySigmaLowering
end LogicLineages.ModelsAlgebra.PGroups.Targets
