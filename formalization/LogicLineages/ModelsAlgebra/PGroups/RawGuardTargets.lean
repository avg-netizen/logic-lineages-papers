module
public import LogicLineages.ModelsAlgebra.PGroups.RawGuardDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def groupRawGuardPiRealization : Prop :=
  ∀ (G : Type u) (R : RawGroupStructure G) (φ : Formula 0),
    (guardPi φ).RawRealize R Fin.elim0 ↔ R.AbelianLaws ∧ φ.RawRealize R Fin.elim0

def groupRawGuardDifferenceRealization : Prop :=
  ∀ (G : Type u) (R : RawGroupStructure G) (d : DifferenceFormula 0),
    (guardDifference d).RawRealize R Fin.elim0 ↔ R.AbelianLaws ∧ d.RawRealize R Fin.elim0

def groupRawGuardPiComplexity : Prop :=
  ∀ (α : Ordinal.{0}), 1 ≤ α → ∀ (φ : Formula 0),
    Complexity .pi α φ → Complexity .pi α (guardPi φ)

def groupRawGuardDifferenceComplexity : Prop :=
  ∀ (α : Ordinal.{0}), 1 ≤ α → ∀ (d : DifferenceFormula 0),
    d.AtLevel α → (guardDifference d).AtLevel α

end LogicLineages.ModelsAlgebra.PGroups.Targets
