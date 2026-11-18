module
public import LogicLineages.CartierObserverCurrent.FullTransientTargets
@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.HigherPolesGeometry.Targets
def GeometricRemoval : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [CharP K 2] [PerfectRing K 2] [CharP L 2] [PerfectRing L 2],
    ∀ σ : K →+* L, ∀ d : Nat, 1 ≤ d → ∀ P : Polynomial K,
    P.degree < (SourceBudget.denominator K d).degree →
    let f : RatFunc K := algebraMap (Polynomial K) (RatFunc K) P /
      algebraMap (Polynomial K) (RatFunc K) (SourceBudget.denominator K d)
    let state : Nat → RatFunc L := fun j => Naturality.rationalMap σ
      ((Basic.actualDifferentialCartier (K := K))^[j] f)
    let a := SourceBudget.transient d
    (∀ j : Nat, MixedProper.proper (state j)) ∧
    (∀ j : Nat, ∀ z : L, PoleContraction.poleOrder z (state (a + j)) ≤ 1)
end LogicLineages.CartierObserverCurrent.HigherPolesGeometry.Targets
