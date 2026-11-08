module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalBoundedDescentNormalizer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The zero case is unconditional for arbitrary leaves. The strict descent
guard, not validity or an assumed fixed-point equation, must force T(0)=0. -/
def ActualOriginalBoundedDescentZero : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Gamma : List (Formula α)),
  Nonempty (Derivation body Gamma
    (transitionGraph representative valid OrdinaryArithmetic.zeroTerm
      OrdinaryArithmetic.zeroTerm))

/-- The stronger induction target includes fuel=0 and arbitrary symbolic
initial values. The bound and repeat graph are object-language hypotheses;
there is no semantic descent, termination, preservation or fixed-point premise. -/
def ActualOriginalBoundedDescentFuelFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Gamma : List (Formula α)) (out fuel value : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((atMost value fuel ⊓
      InternalNumericIteration.repeatGraph (transition representative valid) out fuel value).imp
        (transitionGraph representative valid out out)))

/-- The final numeric output is bounded by the original input, on all inputs. -/
def ActualOriginalBoundedDescentNormalizerBound : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Gamma : List (Formula α)) (out input : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input).imp (atMost out input)))

/-- The conclusion is the graph T(out,out), not B(out,out), and it has no
validity or canonicality antecedent. Stabilization must be derived internally. -/
def ActualOriginalBoundedDescentNormalizerFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Gamma : List (Formula α)) (out input : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input).imp
      (transitionGraph representative valid out out)))

/-- Exact-one validity is preserved when it holds at the original input.
Neither leaf is assumed calibrated, Boolean-valued, or validity preserving. -/
def ActualOriginalBoundedDescentNormalizerValidity : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Gamma : List (Formula α)) (out input : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input).imp
      ((validGraph valid input).imp (validGraph valid out))))

/-- The actual original left-selector graph is preserved for an arbitrary
symbolic type tag, even on malformed inputs and without a validity premise. -/
def ActualOriginalBoundedDescentNormalizerLeft : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Gamma : List (Formula α)) (out input typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input).imp
      ((leftGraph typ input).imp (leftGraph typ out))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerTargets
