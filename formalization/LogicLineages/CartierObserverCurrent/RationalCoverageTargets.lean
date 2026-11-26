module
public import LogicLineages.CartierObserverCurrent.RationalCoverageDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RationalCoverage.Targets
open SplittingRoots RootInterpolation

def StatePresentation : Prop := ∀ d : Nat, ∀ f : RatFunc (FieldAt d),
  state d f ↔ ∃ U : Polynomial (FieldAt d),
    U.degree < (rootProduct d).degree ∧ f = fraction d U

def NumeratorDegree : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  (tupleNumerator d b).degree < (rootProduct d).degree

def NumeratorEvaluation : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d, ∀ z : Root d,
  (tupleNumerator d b).eval z.val = b z * (omittedProduct d z.val).eval z.val

def ActualPartialFraction : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  reconstruct d b = fraction d (tupleNumerator d b)

def ReconstructionInjective : Prop := ∀ d : Nat, Function.Injective (reconstruct d)

def ReconstructionCoverage : Prop := ∀ d : Nat, ∀ f : RatFunc (FieldAt d),
  state d f ↔ ∃! b : Root d → FieldAt d, reconstruct d b = f
end LogicLineages.CartierObserverCurrent.RationalCoverage.Targets
