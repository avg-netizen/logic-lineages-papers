module
public import LogicLineages.CartierObserverCurrent.InitialPrincipalPartsDefinitions
public import LogicLineages.CartierObserverCurrent.SplittingRootsProof

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.RepeatedCartier.Targets
open Basic

/-- Every actual initial simple pole undergoes precisely inverse Frobenius. -/
def SimpleIteration : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K, ∀ ell : Nat,
    (actualDifferentialCartier (K := K))^[ell]
      (rationalC b / (rationalX - rationalC z)) =
    rationalC (((frobeniusEquiv K 2).symm)^[ell] b) / (rationalX - rationalC z)

/-- Higher initial poles cannot turn simple under repeated odd Cartier.
The quantitative cutoff includes ell=0, where no k satisfies the hypotheses. -/
def HigherVanishing : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K,
    ∀ ell k : Nat, 1 < k → k ≤ 2 ^ ell →
      (actualDifferentialCartier (K := K))^[ell]
        (rationalC b / (rationalX - rationalC z) ^ k) = 0

/-- Genuine finite rational sums commute with iteration, not a vector update oracle. -/
def FiniteAdditivity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ n ell : Nat, ∀ f : Fin n → RatFunc K,
      (actualDifferentialCartier (K := K))^[ell] (∑ j, f j) =
        ∑ j, (actualDifferentialCartier (K := K))^[ell] (f j)

/-- All initial principal terms reduce to the inverse-Frobenius simple coefficients.
M>0 makes the initial coefficient at index0 meaningful; all source uses satisfy it. -/
def PrincipalReduction : Prop := ∀ d M : Nat, ∀ hM : 0 < M,
  ∀ b : InitialPrincipalParts.Coefficients d M, ∀ ell : Nat, M ≤ 2 ^ ell →
    (actualDifferentialCartier (K := SplittingRoots.FieldAt d))^[ell]
        (InitialPrincipalParts.reconstruct d M b) =
      RationalCoverage.reconstruct d (fun z =>
        ((frobeniusEquiv (SplittingRoots.FieldAt d) 2).symm)^[ell] (b z ⟨0, hM⟩))
end LogicLineages.CartierObserverCurrent.RepeatedCartier.Targets
