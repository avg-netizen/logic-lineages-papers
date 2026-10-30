module

public import LogicLineages.ModelsAlgebra.PGroups.UlmLowerFormulaDefinitions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
open scoped BigOperators
universe u v

def groupFiniteSumTermEvaluation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n m : ℕ) (f : Fin m → GroupTerm n) (a : Fin n → G),
    (finiteSumTerm m f).eval a = ∑ i, (f i).eval a

def groupUlmLowerMatrixRealization : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] (j n m : ℕ)
    (a : Fin n → G) (d : Fin m → G) (z : Fin 1 → G),
      (ulmLowerMatrix p j n m).Realize (append (append a d) z) ↔
        (∀ i, p • (p ^ j • d i) = 0) ∧
          ∀ r : Fin m → ZMod p, r ≠ 0 →
            p ^ (j + 1) • z 0 ≠ ∑ i, (r i).val • (p ^ j • d i)

def groupUlmLowerWitnessFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n m : ℕ),
    Complexity .pi (1 : Ordinal.{v}) (ulmLowerWitnessFormula p j n m) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G) (d : Fin m → G),
        (ulmLowerWitnessFormula p j n m).Realize (append a d) ↔
          IndependentRootWitnesses p j d

/-- Actual representative and p^j-root lifting is proved in both directions;
no quotient representative/root supplier or dimension convention is assumed. -/
def groupUlmRootRepresentatives : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] (j m : ℕ),
    (∃ d : Fin m → G, IndependentRootWitnesses p j d) ↔
      ∃ v : Fin m → UlmLayer p (finiteFiltration p j : AddSubgroup G),
        LinearIndependent (ZMod p) v

/-- Concrete Sigma_2 lower-bound formula for genuine quotient independence,
including the empty family. No finrank/rank replacement is made here. -/
def groupUlmLowerFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n m : ℕ),
    Complexity .sigma (2 : Ordinal.{v}) (ulmLowerFormula p j n m) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (ulmLowerFormula p j n m).Realize a ↔
          ∃ v : Fin m → UlmLayer p (finiteFiltration p j : AddSubgroup G),
            LinearIndependent (ZMod p) v

end LogicLineages.ModelsAlgebra.PGroups.Targets
