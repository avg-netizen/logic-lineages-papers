module
public import LogicLineages.CartierObserverCurrent.ProfileDescentDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ProfileDescent.Targets
open SplittingRoots

def FrobeniusTransport : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  Naturality.rationalMap (frobenius (FieldAt d) 2) (RationalCoverage.reconstruct d b) =
    RationalCoverage.reconstruct d (transport d b)

def CompatibilityFixed : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  compatible d b ↔
    Naturality.rationalMap (frobenius (FieldAt d) 2) (RationalCoverage.reconstruct d b) =
      RationalCoverage.reconstruct d b

def ProfileToBase : Prop := ∀ d : Nat, ∀ b : Root d → FieldAt d,
  compatible d b ↔ ∃! g : RatFunc (ZMod 2),
    baseState d g ∧ extend d g = RationalCoverage.reconstruct d b

def BaseToProfile : Prop := ∀ d : Nat, ∀ g : RatFunc (ZMod 2), baseState d g →
  ∃! b : Root d → FieldAt d,
    compatible d b ∧ RationalCoverage.reconstruct d b = extend d g
end LogicLineages.CartierObserverCurrent.ProfileDescent.Targets
