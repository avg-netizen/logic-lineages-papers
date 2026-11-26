module
public import LogicLineages.CartierObserverCurrent.ProfileOutputDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileOutput.Targets
open SplittingRoots

def ProductRegular : Prop := ∀ d : Nat, (RootInterpolation.rootProduct d).eval 0 ≠ 0

def NumeratorRatio : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  (RationalCoverage.tupleNumerator d b).eval 0 / (RootInterpolation.rootProduct d).eval 0 = value d b

def ActualSeriesOutput : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  (FractionSeries.seriesFraction (RationalCoverage.tupleNumerator d b)
    (RootInterpolation.rootProduct d)).coeff 0 = value d b

def OutputDescent : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  ProfileDescent.compatible d b →
    ∃! a : ZMod 2, algebraMap (ZMod 2) (FieldAt d) a = value d b

def ActualBaseOutput : Prop := ∀ d : Nat, ∀ g : RatFunc (ZMod 2), ∀ b : Root d → FieldAt d,
  ProfileDescent.extend d g = RationalCoverage.reconstruct d b →
    g.denom.eval 0 ≠ 0 ∧
    algebraMap (ZMod 2) (FieldAt d)
      ((FractionSeries.seriesFraction g.num g.denom).coeff 0) = value d b
end LogicLineages.CartierObserverCurrent.ProfileOutput.Targets
