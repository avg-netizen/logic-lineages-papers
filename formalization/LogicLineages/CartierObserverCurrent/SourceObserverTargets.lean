module
public import LogicLineages.CartierObserverCurrent.SourceObserverDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SourceObserver.Targets
open SplittingRoots

def PresentedExpansion : Prop := ∀ d : Nat, ∀ P : Polynomial (ZMod 2),
  RegularSelectors.regular (initial d P) ∧
  RegularSelectors.expansion (initial d P) =
    FractionSeries.seriesFraction P (SourceBudget.denominator (ZMod 2) d)

def ExactSourceContinuations : Prop := ∀ d : Nat, 1 ≤ d → ∀ P : Polynomial (ZMod 2),
  P.degree < (SourceBudget.denominator (ZMod 2) d).degree → ∀ p : List Bool,
  SourceBudget.transient d ≤ p.length → ∃! b : Root d → FieldAt d,
    ProfileDescent.compatible d b ∧
    RationalCoverage.reconstruct d b = SourceState.run d P p ∧
    ∀ w : List Bool, ProfileOutput.value d (AllWordObserver.execute d w b) =
      algebraMap (ZMod 2) (FieldAt d)
        ((FractionSeries.seriesFraction P (SourceBudget.denominator (ZMod 2) d)).coeff
          (AllWordObserver.offset p + 2 ^ p.length * AllWordObserver.offset w))
end LogicLineages.CartierObserverCurrent.SourceObserver.Targets
