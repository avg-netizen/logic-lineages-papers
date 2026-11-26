module
public import LogicLineages.CartierObserverCurrent.RootInterpolationDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RootInterpolation.Targets
open SplittingRoots

def ProductDegree : Prop := ∀ d : Nat,
  (rootProduct d).Monic ∧ (rootProduct d).natDegree = (rootSet d).card

def OmittedFactor : Prop := ∀ d : Nat, ∀ z : Root d,
  rootProduct d = (Polynomial.X - Polynomial.C z.val) * omittedProduct d z.val

def OmittedNonzero : Prop := ∀ d : Nat, ∀ z : Root d,
  (omittedProduct d z.val).eval z.val ≠ 0

def OmittedDegree : Prop := ∀ d : Nat, ∀ z : Root d,
  (omittedProduct d z.val).degree < ((rootSet d).card : WithBot Nat)

def InterpolationNodes : Prop := ∀ d : Nat, ∀ U : Polynomial (FieldAt d),
  ∀ z : Root d, (interpolate d U).eval z.val = U.eval z.val

def InterpolationComplete : Prop := ∀ d : Nat, ∀ U : Polynomial (FieldAt d),
  U.degree < ((rootSet d).card : WithBot Nat) → interpolate d U = U
end LogicLineages.CartierObserverCurrent.RootInterpolation.Targets
