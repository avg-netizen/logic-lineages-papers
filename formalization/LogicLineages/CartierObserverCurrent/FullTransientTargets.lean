module
public import LogicLineages.CartierObserverCurrent.SourceBudgetTargets
public import LogicLineages.CartierObserverCurrent.PoleContractionTargets
public import LogicLineages.CartierObserverCurrent.MixedProperTargets
public import LogicLineages.CartierObserverCurrent.NaturalityTargets

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.FullTransient.Targets

/-- Complete printed binary transient, including actual extension-field geometric
coordinates and every mixed word. d>=1 keeps the source ceiling logarithm positive-domain. -/
def BinaryTransient : Prop :=
  MixedProper.Targets.StepProper.{u} ∧
  PoleContraction.Targets.CanonicalPoleContraction.{u} ∧
  PoleContraction.Targets.NoNewPole.{u} ∧
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [CharP K 2] [PerfectRing K 2] [CharP L 2] [PerfectRing L 2],
    ∀ σ : K →+* L, ∀ d : Nat, 1 ≤ d → ∀ P : Polynomial K,
    P.degree < (SourceBudget.denominator K d).degree → ∀ w : List Bool,
    let f : RatFunc K := algebraMap (Polynomial K) (RatFunc K) P /
      algebraMap (Polynomial K) (RatFunc K) (SourceBudget.denominator K d)
    let g : RatFunc L := Naturality.rationalMap σ (MixedWord.execute w f)
    MixedProper.proper g ∧
    (∀ z : L, PoleContraction.poleOrder z (Naturality.rationalMap σ f) = 0 →
      PoleContraction.poleOrder z g = 0) ∧
    (SourceBudget.transient d ≤ w.length → ∀ z : L,
      PoleContraction.poleOrder z g ≤ 1)
end LogicLineages.CartierObserverCurrent.FullTransient.Targets
