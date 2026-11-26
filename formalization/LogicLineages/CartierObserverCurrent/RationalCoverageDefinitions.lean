module
public import LogicLineages.CartierObserverCurrent.RootInterpolationDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RationalCoverage
open SplittingRoots RootInterpolation

/-- Independent canonical rational-state predicate, not an image predicate. -/
def state (d : Nat) (f : RatFunc (FieldAt d)) : Prop :=
  MixedProper.proper f ∧ f.denom ∣ rootProduct d

noncomputable def fraction (d : Nat) (U : Polynomial (FieldAt d)) : RatFunc (FieldAt d) :=
  algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) U /
    algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) (rootProduct d)

noncomputable def tupleNumerator (d : Nat) (b : Root d → FieldAt d) : Polynomial (FieldAt d) := by
  classical
  letI : Fintype (Root d) := by unfold Root; infer_instance
  exact ∑ z : Root d, Polynomial.C (b z) * omittedProduct d z.val

/-- Genuine rational simple-pole sum for an arbitrary complete tuple. -/
noncomputable def reconstruct (d : Nat) (b : Root d → FieldAt d) : RatFunc (FieldAt d) := by
  classical
  letI : Fintype (Root d) := by unfold Root; infer_instance
  exact ∑ z : Root d,
    (algebraMap (FieldAt d) (RatFunc (FieldAt d)) (b z)) /
      (Basic.rationalX - algebraMap (FieldAt d) (RatFunc (FieldAt d)) z.val)
end LogicLineages.CartierObserverCurrent.RationalCoverage
