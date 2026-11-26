module
public import LogicLineages.CartierObserverCurrent.PoleContractionDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PoleContraction.Targets

def ActualRootFactorization : Prop :=
  ∀ (K : Type u) [Field K], ∀ Q : Polynomial K, Q ≠ 0 → ∀ z : K,
    Q = (Polynomial.X - Polynomial.C z) ^ Q.rootMultiplicity z * rootRemoved Q z ∧
    (rootRemoved Q z).eval z ≠ 0

def FractionPoleContraction : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ P Q : Polynomial K, Q ≠ 0 → ∀ b : Bool, ∀ z : K,
      poleOrder z (MixedProper.step b
        (algebraMap (Polynomial K) (RatFunc K) P /
          algebraMap (Polynomial K) (RatFunc K) Q)) ≤ (Q.rootMultiplicity z + 1) / 2

def CanonicalPoleContraction : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ f : RatFunc K, ∀ b : Bool, ∀ z : K,
      poleOrder z (MixedProper.step b f) ≤ (poleOrder z f + 1) / 2

def NoNewPole : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ f : RatFunc K, ∀ b : Bool, ∀ z : K,
      poleOrder z f = 0 → poleOrder z (MixedProper.step b f) = 0
end LogicLineages.CartierObserverCurrent.PoleContraction.Targets
