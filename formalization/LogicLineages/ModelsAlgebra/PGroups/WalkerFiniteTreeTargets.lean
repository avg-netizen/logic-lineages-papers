module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiniteTreeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Source finite ancestor-tree normal form, paper01 lines 694–704, generalized
also to finite forests. Every presentation is the literal recursive quotient. -/
def walkerFiniteTreeUniqueDigits : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence, ∀ n : ℕ,
    Function.Bijective (walkerFiniteDigitSum p parent n)

/-- Every node satisfies precisely its advertised root/parent relation. -/
def walkerFiniteTreeRelations : Prop :=
  ∀ p : ℕ, ∀ parent : WalkerParentSequence, ∀ n : ℕ, ∀ i : Fin n,
    p • (walkerFinitePresentation p parent n).generator i =
      (parent i.val).elim 0 (fun j =>
        (walkerFinitePresentation p parent n).generator ⟨j.val, lt_trans j.isLt i.isLt⟩)

end LogicLineages.ModelsAlgebra.PGroups.Targets
