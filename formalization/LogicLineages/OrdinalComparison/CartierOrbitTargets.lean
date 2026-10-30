module
public import LogicLineages.OrdinalComparison.CartierOrbitDefinitions
public import LogicLineages.OrdinalComparison.CartierLaurentTargets

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Genuine initial-state and all-iteration bridge for the final sentence
of source thm:actual-period. No residue/state transport premise is assumed. -/
def ActualLinkedDifferentialInitialResidue : Prop :=
  ∀ u : Nat, 5 ≤ u → ∀ z : ActualPrimitiveRootIndex u,
    (actualTranslatedRationalEmbedding z.val (actualLinkedDifferential u)).coeff (-1) =
      actualResidueTuple u z

def ActualDifferentialCartierIteratedResidue : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z : K, ∀ f : RatFunc K,
    ∀ j : Nat,
      (actualTranslatedRationalEmbedding z ((actualDifferentialCartier (K := K))^[j] f)).coeff (-1) =
        (iterateFrobeniusEquiv K 2 j).symm ((actualTranslatedRationalEmbedding z f).coeff (-1))

end LogicLineages.OrdinalComparison.Targets
