module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedDifferenceIndexDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def reducedNoLimitDifferenceIndex : Prop :=
  ∀ (G:Type) [AddCommGroup G] [Countable G] (p:ℕ) [Fact p.Prime],
    (∀x:G,∃k:ℕ,p^k • x=0) → IsReducedAddGroup G →
    ∀ α:Ordinal.{0}, Order.IsSuccLimit α → ¬ RawDifferenceEndpoint G α
def rawNoZeroDifferenceScott : Prop :=
  ∀ (G:Type) [AddCommGroup G] [Countable G] (d:DifferenceFormula 0),
    d.AtLevel (0:Ordinal.{0}) → ¬ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
end LogicLineages.ModelsAlgebra.PGroups.Targets
