module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Fixed source-comparison statements for paper 15

This module imports no project implementation. The specifications use
Mathlib's actual derivations, algebraicity and field structures. Proofs
are supplied and checked separately in `StatementChecks.lean`.
-/

namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

set_option maxHeartbeats 20000

/-- Paper 15, Lemma `lem:constants`, over the rational base. -/
def algebraicConstants : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℚ F F)
    (x : F), IsAlgebraic ℚ x → D x = 0

/-- The nonconstant-implies-transcendental conclusion of that lemma. -/
def nonconstantTranscendental : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (D : Derivation ℚ F F)
    (x : F), D x ≠ 0 → Transcendental ℚ x

end LogicLineages.ModelsAlgebra.Differential.Targets
