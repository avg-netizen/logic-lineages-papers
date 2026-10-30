module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

/-- Actual direct-limit preservation, with no assumed chain or isocopy fields. -/
def groupEndomorphismLimitPiTwo : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (f : G →+ G), Function.Injective f →
    ∀ φ : Formula 0, Complexity .pi (2 : Ordinal.{v}) φ →
      φ.Realize (Fin.elim0 : Fin 0 → G) →
        φ.Realize (Fin.elim0 : Fin 0 → EndomorphismLimit f)

end LogicLineages.ModelsAlgebra.PGroups.Targets
