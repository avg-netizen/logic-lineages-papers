module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions
public import LogicLineages.OrdinalComparison.NormBalls

@[expose] public section

/-! Source-domain finite norm balls, independently specified on actual ordinals.

Paper 05, `foundations.tex`, `lem:finite-balls`. The second statement gives
exact membership in the finite semantic image of the existing notation
iterator. It does not assert Mathlib encoded computability on raw Ordinal,
or by itself discharge the source's remaining effectiveness obligations.
Only previously checked suppliers are imported, not new transport proofs.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualFiniteNormBalls : Prop :=
  ∀ b : Nat, Set.Finite {a : Ordinal.{0} | a < epsilonZero ∧ actualOrdinalNorm a ≤ b}

def ActualNormBallDenotationMembership : Prop := by
  classical
  exact ∀ (b : Nat) (a : Ordinal.{0}),
    a ∈ (notationNormBall b).image (fun n => n.1.repr) ↔
      a < epsilonZero ∧ actualOrdinalNorm a ≤ b

end LogicLineages.OrdinalComparison.Targets
