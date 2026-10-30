module
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScottDefinitions
public import Mathlib.Order.Monotone.Defs
public import Mathlib.SetTheory.Ordinal.Arithmetic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupPiTwoTupleRetractReflection : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (i : H →+ G),
    Function.Injective i →
    (∀ (m : ℕ) (d : Fin m → H), ∃ f : G →+ H,
      Function.Injective f ∧ ∀ j, f (i (d j)) = d j) →
    ∀ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ →
      φ.Realize (Fin.elim0 : Fin 0 → G) → φ.Realize (Fin.elim0 : Fin 0 → H)

/-- Actual finite-tuple maps and a real covered chain, not a reflection oracle. -/
def groupDifferenceTwoStageReflection : Prop :=
  ∀ (G : Type) [AddCommGroup G] (S : ℕ → AddSubgroup G),
    Monotone S → (∀ g : G, ∃ i, g ∈ S i) →
    (∀ (i m : ℕ) (d : Fin m → S i), ∃ f : G →+ S i,
      Function.Injective f ∧ ∀ j, f (d j : G) = d j) →
    ∀ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) →
      d.Realize (Fin.elim0 : Fin 0 → G) →
        ∃ i, d.Realize (Fin.elim0 : Fin 0 → S i)

/-- Generic chain obstruction; the concrete source chain must prove its hypotheses. -/
def groupChainNoDifferenceTwoScott : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (S : ℕ → AddSubgroup G),
    Monotone S → (∀ g : G, ∃ i, g ∈ S i) →
    (∀ (i m : ℕ) (d : Fin m → S i), ∃ f : G →+ S i,
      Function.Injective f ∧ ∀ j, f (d j : G) = d j) →
    (∀ i, ¬ Nonempty (G ≃+ S i)) →
    ∀ d : DifferenceFormula 0, d.AtLevel (2 : Ordinal.{0}) → ¬ DifferenceScottSentence G d

end LogicLineages.ModelsAlgebra.PGroups.Targets
