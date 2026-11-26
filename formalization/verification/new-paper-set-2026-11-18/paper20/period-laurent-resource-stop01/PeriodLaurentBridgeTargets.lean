module
public import LogicLineages.OrdinalComparison.CartierOrbitDefinitions
public import LogicLineages.OrdinalComparison.TranslatedRationalDefinitions
public import LogicLineages.CartierObserverCurrent.BasicRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodLaurentBridge.Targets
open LogicLineages.OrdinalComparison

/-- Exact old/current actual operations, not a quotient or an observation equivalence. -/
def CartierIdentity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    LogicLineages.OrdinalComparison.actualDifferentialCartier f = Basic.actualDifferentialCartier f

/-- Genuine translated rational-to-Hahn embedding; arbitrary rational inputs and
ALL integer indices, including negative exponents at poles. -/
def LaurentCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ z : K, ∀ f : RatFunc K, ∀ n : Int,
      (actualTranslatedRationalEmbedding z (Basic.actualDifferentialCartier f)).coeff n =
        (frobeniusEquiv K 2).symm
          ((actualTranslatedRationalEmbedding z f).coeff (2 * n + 1))

/-- The actual source rational input really has the independently defined initial
Laurent residue tuple, deriving source root/derivative conditions internally. -/
def InitialResidue : Prop := ∀ u : Nat, 5 ≤ u → ∀ z : ActualPrimitiveRootIndex u,
  (actualTranslatedRationalEmbedding z.val (actualLinkedDifferential u)).coeff (-1) =
    actualResidueTuple u z

/-- All iterations of the exact legacy operation used in the frozen theorem.
No regularity, simple-pole, initial-residue or transport premise is supplied. -/
def IteratedResidue : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2],
    ∀ z : K, ∀ f : RatFunc K, ∀ j : Nat,
      (actualTranslatedRationalEmbedding z
        ((LogicLineages.OrdinalComparison.actualDifferentialCartier (K := K))^[j] f)).coeff (-1) =
        (iterateFrobeniusEquiv K 2 j).symm
          ((actualTranslatedRationalEmbedding z f).coeff (-1))
end LogicLineages.CartierObserverCurrent.PeriodLaurentBridge.Targets
