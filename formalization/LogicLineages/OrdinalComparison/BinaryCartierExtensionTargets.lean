module
public import LogicLineages.OrdinalComparison.BinaryCartierExtensionDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

def ActualBinaryRationalExtensionInjective : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K],
    Function.Injective (actualBinaryRationalExtension K)

def ActualBinaryRationalExtensionPolynomial : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ U : Polynomial (ZMod 2),
    actualBinaryRationalExtension K (algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) U) =
      algebraMap (Polynomial K) (RatFunc K) (U.map (algebraMap (ZMod 2) K))

def ActualBinaryRationalExtensionCartier : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K] [CharP K 2] [PerfectRing K 2],
    ∀ f : RatFunc (ZMod 2),
      actualBinaryRationalExtension K (actualDifferentialCartier f) =
        actualDifferentialCartier (actualBinaryRationalExtension K f)

def ActualBinaryRationalExtensionLinked : Prop :=
  ∀ u : Nat,
    actualBinaryRationalExtension ActualResidueField
      (actualBinaryRationalDifferential (actualLinkedCutoff u)
        (Polynomial.X ^ (actualLinkedOffset u - 1) : Polynomial (ZMod 2))) =
      actualLinkedDifferential u

end LogicLineages.OrdinalComparison.Targets
