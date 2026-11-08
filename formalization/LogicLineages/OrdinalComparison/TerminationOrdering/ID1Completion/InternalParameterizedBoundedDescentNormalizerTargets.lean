module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalParameterizedBoundedDescentNormalizer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Unconditionally T(0,parameter)=0 for arbitrary binary leaves and every
symbolic parameter, including nonzero ones. The candidate < 0 guard, not a
fixed-point, validity or carried-state-zero assumption, forces rejection. -/
def ActualOriginalParameterizedBoundedDescentZero : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 2) (α : Type)
    (Gamma : List (Formula α)) (parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    (transitionGraph representative valid OrdinaryArithmetic.zeroTerm
      OrdinaryArithmetic.zeroTerm parameter))

/-- Strong internal stabilization measures the VALUE against the symbolic
fuel. repeatGraph is the actual repeatP graph, which carries the identical
parameter. It includes fuel=0 with arbitrary, possibly nonzero parameter;
there is no bound on pair(parameter,value), parameter, or its left tag. -/
def ActualOriginalParameterizedBoundedDescentFuelFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 2) (α : Type)
    (Gamma : List (Formula α)) (out fuel value parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((atMost value fuel ⊓
      InternalParameterizedNumericIteration.repeatGraph
        (transition representative valid) out fuel value parameter).imp
        (transitionGraph representative valid out out parameter)))

/-- The final VALUE is bounded by the original VALUE at every parameter,
including malformed inputs. No source-validity premise is supplied. -/
def ActualOriginalParameterizedBoundedDescentNormalizerBound : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 2) (α : Type)
    (Gamma : List (Formula α)) (out input parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input parameter).imp (atMost out input)))

/-- The actual binary transition fixes the full output at the SAME
symbolic parameter: T(out,parameter)=out, not B-fixed or R-fixed. -/
def ActualOriginalParameterizedBoundedDescentNormalizerFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 2) (α : Type)
    (Gamma : List (Formula α)) (out input parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input parameter).imp
      (transitionGraph representative valid out out parameter)))

/-- Exact-one validity is preserved at the identical symbolic parameter.
Both binary leaves are arbitrary; neither has a calibration, Boolean-range,
preservation, canonicality or termination assumption. -/
def ActualOriginalParameterizedBoundedDescentNormalizerValidity : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 2) (α : Type)
    (Gamma : List (Formula α)) (out input parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input parameter).imp
      ((validGraph valid input parameter).imp (validGraph valid out parameter))))

/-- Preserve the ORIGINAL left tag of the VALUE for every symbolic type
tag, independently of the carried parameter and without validity premises.
Preserving left(pair(parameter,value)) alone would not meet this target. -/
def ActualOriginalParameterizedBoundedDescentNormalizerLeft : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 2) (α : Type)
    (Gamma : List (Formula α)) (out input typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((normalizerGraph representative valid out input parameter).imp
      ((leftGraph typ input).imp (leftGraph typ out))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerTargets
