module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedUlmClassificationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Actual least zero stage, with no externally supplied length invariant. -/
def PGroupExactLength (p:ℕ) (G:Type) [AddCommGroup G] (ell:Ordinal.{0}) : Prop :=
  (transfiniteFiltration p ell : AddSubgroup G)=⊥ ∧
    ∀ α<ell, (transfiniteFiltration p α : AddSubgroup G)≠⊥
end LogicLineages.ModelsAlgebra.PGroups
