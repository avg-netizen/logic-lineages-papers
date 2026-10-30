module
public import LogicLineages.ModelsAlgebra.PGroups.RawGroupAxiomsDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupRawAxiomsComplexity : Prop := Complexity .pi (1 : Ordinal.{0}) abelianGroupAxioms

def groupRawAxiomsRealization : Prop :=
  ∀ (G : Type u) (R : RawGroupStructure G),
    abelianGroupAxioms.RawRealize R (Fin.elim0 : Fin 0 → G) ↔ R.AbelianLaws

def groupRawLawsGroupConstruction : Prop :=
  ∀ (G : Type u) (R : RawGroupStructure G), R.AbelianLaws →
    ∃ inst : AddCommGroup G, @RawGroupStructure.ofGroup G inst = R

end LogicLineages.ModelsAlgebra.PGroups.Targets
