module
public import LogicLineages.OrdinalComparison.PoleMultiplicityDefinitions

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual root multiplicity to local Laurent support, a supplier for source
lem:poles. The literal source A_d and uniform μ bound remain separate. -/
def ActualMultiplicityPoleExpansion : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, A ≠ 0 → ∀ z : K,
    actualTranslatedRationalEmbedding z
      (algebraMap (Polynomial K) (RatFunc K) U / algebraMap (Polynomial K) (RatFunc K) A) =
        actualMultiplicityPoleExpansion A U z

def ActualMultiplicityPoleLowerSupport : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, A ≠ 0 → ∀ z : K,
    ∀ n : Int, n < -(A.rootMultiplicity z : Int) →
      (actualTranslatedRationalEmbedding z
        (algebraMap (Polynomial K) (RatFunc K) U / algebraMap (Polynomial K) (RatFunc K) A)).coeff n = 0

end LogicLineages.OrdinalComparison.Targets
