module
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Actual nonzero-limit Scott lowering, including arbitrary raw structures
in the original signature. No orbit-definability or Miller oracle. -/
def rawLimitSigmaScottLowering : Prop :=
  ∀ (G : Type) [Countable G] (R : RawGroupStructure G)
    (α : Ordinal.{0}) [Countable α.ToType], Order.IsSuccLimit α →
    ∀ φ : Formula 0, Complexity .sigma α φ → RawScottSentence R φ →
    ∃ β : Ordinal.{0}, β < α ∧ ∃ ψ : Formula 0,
      Complexity .sigma β ψ ∧ RawScottSentence R ψ
end LogicLineages.ModelsAlgebra.PGroups.Targets
