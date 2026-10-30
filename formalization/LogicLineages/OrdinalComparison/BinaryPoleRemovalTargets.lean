module
public import LogicLineages.OrdinalComparison.BinaryPoleRemovalDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Whole source paper10 lem:poles: no actual initial-support or properness
preservation premise is borrowed. μ and its ceiling-log transient are literal.
All finite coordinates are quantified, and all later states remain proper. -/
def FullActualBinaryHigherPoleRemoval : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K] [CharP K 2] [PerfectRing K 2],
    ∀ d : Nat, ∀ U : Polynomial K,
    U.degree < ((actualBinarySourceDenominator d).map (algebraMap (ZMod 2) K)).degree →
    (∀ j : Nat, actualRationalProper
      ((actualDifferentialCartier (K := K))^[j] (actualBinaryRationalDifferential d U))) ∧
    (∀ z : K, ∀ n : Int, n < -1 →
      (actualTranslatedRationalEmbedding z
        ((actualDifferentialCartier (K := K))^[actualBinaryPoleTransient d]
          (actualBinaryRationalDifferential d U))).coeff n = 0) ∧
    (∀ z : K, ∀ j : Nat,
      (actualTranslatedRationalEmbedding z
        ((actualDifferentialCartier (K := K))^[actualBinaryPoleTransient d + j]
          (actualBinaryRationalDifferential d U))).coeff (-1) =
        (iterateFrobeniusEquiv K 2 j).symm
          ((actualTranslatedRationalEmbedding z
            ((actualDifferentialCartier (K := K))^[actualBinaryPoleTransient d]
              (actualBinaryRationalDifferential d U))).coeff (-1)))

end LogicLineages.OrdinalComparison.Targets
