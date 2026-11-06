module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionTargets
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof InternalCalculus SourceEndpoint TaggedArithmeticOperators

/-- Introduce the ORIGINAL tag-guarded branch from its own original payload.
The target is an actual closed proof, not standard-N equivalence. -/
def ActualTaggedBranchIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (odd : Bool) (p : Positive (Fin 2))
    (context t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((substitutePositive ![context,t] (tagPredicate odd p)).formula.imp
      (substitutePositive ![context,tagTerm odd t] (taggedBranch odd p)).formula))

/-- The opposite ORIGINAL guard is internally vacuous by the original tag
arithmetic. No assertion about its source payload is assumed. -/
def ActualOppositeBranch : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (odd : Bool) (p : Positive (Fin 2))
    (context t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (substitutePositive ![context,tagTerm odd t] (taggedBranch (!odd) p)).formula)

/-- Exact internal I fixed-point equation with original carrier and all
original R successors, derived in the one unchanged combined-body calculus. -/
def ActualInternalScalarEquation : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm false t)).formula.iff
      (substitutePositive ![numeral context,t] (tagPredicate false (SourcePresentation.scalarOperator data))).formula))

/-- Exact internal J equation for the original typed list/direct relation. -/
def ActualInternalMultisetEquation : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm true t)).formula.iff
      (substitutePositive ![numeral context,t] (tagPredicate true (SourcePresentation.multisetOperator data))).formula))

/-- Actual joint-Gamma Programs precede every context and term; neither
source closure nor an internal derivability premise is supplied by the caller. -/
def ActualUniformEquationsExist : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ data : SourcePresentation.Data,
  ContextUniform.Calibrated data n arity ∧
  ∀ (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm false t)).formula.iff
      (substitutePositive ![numeral context,t] (tagPredicate false (SourcePresentation.scalarOperator data))).formula)) ∧
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm true t)).formula.iff
      (substitutePositive ![numeral context,t] (tagPredicate true (SourcePresentation.multisetOperator data))).formula))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionTargets
