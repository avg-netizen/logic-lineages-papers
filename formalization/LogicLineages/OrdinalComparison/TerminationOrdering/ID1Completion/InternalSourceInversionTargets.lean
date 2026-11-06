module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionTargets
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof InternalCalculus SourceEndpoint TaggedArithmeticOperators

/-- Logical elimination of the ORIGINAL numerical tag guard, using reflexivity
at its own tag. This needs no tag parity/disjointness or arithmetic oracle. -/
def ActualTaggedBranchElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (odd : Bool) (p : Positive (Fin 2))
    (context t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((substitutePositive ![context,tagTerm odd t] (taggedBranch odd p)).formula.imp
      (substitutePositive ![context,t] (tagPredicate odd p)).formula))

/-- An actual closed internal proof: scalar membership yields the ORIGINAL
carrier and universally guarded R-successor membership formula. -/
def ActualInternalScalarInversion : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm false t)).formula.imp
      (substitutePositive ![numeral context,t] (tagPredicate false (SourcePresentation.scalarOperator data))).formula))

/-- The same for the ORIGINAL list carrier and direct-multiset relation. -/
def ActualInternalMultisetInversion : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm true t)).formula.imp
      (substitutePositive ![numeral context,t] (tagPredicate true (SourcePresentation.multisetOperator data))).formula))

/-- Separate standard-N calibration of the EXACT conclusions above. This is
not used as a derivation rule or a premise of either internal inversion. -/
def ActualOriginalBranchTruth : Prop :=
  ∀ (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat),
  ContextUniform.Calibrated data n arity → ∀ (context : Nat) (P : Nat → Prop) (x : Nat),
  (realize P (substitutePositive ![numeral context, (.var 0 : OrdinaryArithmetic.Term (Fin 1))]
      (tagPredicate false (SourcePresentation.scalarOperator data))).formula ![x] ↔
    ContextUniform.encodedScalar n arity context x ∧
      ∀ y, ContextUniform.encodedR n arity context x y → P (tagNumber false y)) ∧
  (realize P (substitutePositive ![numeral context, (.var 0 : OrdinaryArithmetic.Term (Fin 1))]
      (tagPredicate true (SourcePresentation.multisetOperator data))).formula ![x] ↔
    ContextUniform.encodedList n arity context x ∧
      ∀ y, ContextUniform.encodedDirect n arity context x y → P (tagNumber true y))

/-- Actual calibrated Programs precede all contexts, parameter types and terms.
No caller computability, closure, or derivability premise is introduced. -/
def ActualUniformInversionExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ data : SourcePresentation.Data,
  ContextUniform.Calibrated data n arity ∧
  ∀ (context : Nat) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm false t)).formula.imp
      (substitutePositive ![numeral context,t] (tagPredicate false (SourcePresentation.scalarOperator data))).formula)) ∧
  Nonempty (Derivation (SourcePresentation.sourceBody data context) []
    ((Positive.predicate (tagTerm true t)).formula.imp
      (substitutePositive ![numeral context,t] (tagPredicate true (SourcePresentation.multisetOperator data))).formula))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionTargets
