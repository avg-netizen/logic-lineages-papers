module
public import LogicLineages.CartierObserverCurrent.SplittingRootsDefinitions
public import LogicLineages.CartierObserverCurrent.NaturalityDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.F2Descent.Targets
open SplittingRoots

def PolynomialDescent : Prop := ∀ d : Nat, ∀ P : Polynomial (FieldAt d),
  P.map (frobenius (FieldAt d) 2) = P ↔
    ∃! Q : Polynomial (ZMod 2),
      Q.map (algebraMap (ZMod 2) (FieldAt d)) = P ∧ Q.degree = P.degree

def RationalDescent : Prop := ∀ d : Nat, ∀ f : RatFunc (FieldAt d),
  Naturality.rationalMap (frobenius (FieldAt d) 2) f = f ↔
    ∃! g : RatFunc (ZMod 2), Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) g = f
end LogicLineages.CartierObserverCurrent.F2Descent.Targets
