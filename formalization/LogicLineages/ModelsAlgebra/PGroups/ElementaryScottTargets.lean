module

public import LogicLineages.ModelsAlgebra.PGroups.ElementaryScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

def groupElementaryAbelianSentence : Prop :=
  ∀ p : ℕ, Complexity .pi (2 : Ordinal.{v}) (elementaryAbelianSentence p) ∧
    ∀ (G : Type u) [AddCommGroup G],
      (elementaryAbelianSentence p).Realize (Fin.elim0 : Fin 0 → G) ↔
        (∀ x : G, p • x = 0) ∧ Infinite G

/-- Genuine exponent-p categoricity in the actual additive-group model domain.
This is not the general bounded-exponent theorem or an encoding of group axioms. -/
def groupElementaryAbelianScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] [Countable G] [Infinite G],
    (∀ x : G, p • x = 0) → GroupScottSentence G (elementaryAbelianSentence p)

end LogicLineages.ModelsAlgebra.PGroups.Targets
