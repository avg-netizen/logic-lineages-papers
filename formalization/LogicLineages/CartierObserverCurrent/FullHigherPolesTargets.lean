module
public import LogicLineages.CartierObserverCurrent.FullTransientTargets
public import LogicLineages.CartierObserverCurrent.PeriodLaurentGenericTargets

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.FullHigherPoles.Targets

/-- True rational iteration is the actual all-odd-selector word. -/
def RepeatedWord : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K, ∀ j : Nat,
    MixedWord.execute (List.replicate j true) f =
      (Basic.actualDifferentialCartier (K := K))^[j] f

/-- Every extension-field finite pole is measured on the genuine canonical
rational denominator. Residues are genuine translated Hahn coefficients. -/
def RemovalAndResidues : Prop :=
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
    (∀ j : Nat, ∀ z : L, PoleContraction.poleOrder z (state (a + j)) ≤ 1) ∧
    (∀ z : L, ∀ j : Nat,
      (LogicLineages.OrdinalComparison.actualTranslatedRationalEmbedding z (state (a + j))).coeff (-1) =
        (iterateFrobeniusEquiv L 2 j).symm
          ((LogicLineages.OrdinalComparison.actualTranslatedRationalEmbedding z (state a)).coeff (-1)))

def CompleteHigherPoles : Prop :=
  RepeatedWord.{u} ∧ PeriodLaurentGeneric.Targets.CartierIdentity.{u} ∧
    Naturality.Targets.ExtensionWord.{u,v} ∧ RemovalAndResidues.{u,v}
end LogicLineages.CartierObserverCurrent.FullHigherPoles.Targets
