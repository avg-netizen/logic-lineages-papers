module
public import Mathlib.GroupTheory.QuotientGroup.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupRetainedSumDisjoint : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (A K T H : AddSubgroup G),
    H = K ⊔ T → Disjoint K T → A ⊓ H ≤ K → Disjoint (A ⊔ K) T

def groupRetainedSumQuotientInjective : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (A K T H : AddSubgroup G),
    H = K ⊔ T → Disjoint K T → A ⊓ H ≤ K →
    Function.Injective (fun x : ↥(A ⊔ K) => (QuotientAddGroup.mk' T) (x : G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
