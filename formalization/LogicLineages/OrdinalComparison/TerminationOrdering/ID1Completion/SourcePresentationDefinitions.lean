module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceEndpointDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentation
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open TaggedArithmeticOperators SourceComputabilityFormulaSupportProof InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Concrete primitive-recursive checker programs. Formulas below are the
literal ordinary arithmetic compiler outputs, rather than arbitrary formulas
chosen by their standard-N extension. -/
structure Data where
  scalar : Program 2
  multiset : Program 2
  positive : Program 4
  direct : Program 4

def Calibrated (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) : Prop :=
  (∀ v, evaluate data.scalar v = OrdinaryArithmeticCarrier.scalarValue n arity Gamma v) ∧
  (∀ v, evaluate data.multiset v = OrdinaryArithmeticCarrier.listValue n arity Gamma v) ∧
  (∀ v, evaluate data.positive v = OrdinaryArithmeticQuotient.positiveValue n arity Gamma v) ∧
  (∀ v, evaluate data.direct v = OrdinaryArithmeticDirect.directValue n arity Gamma v)

def checkerFormula (p : Program 2) : OrdinaryArithmetic.Formula (Fin 2) :=
  OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula p)
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![.var 0,.var 1]

def scalarOperator (data : Data) : Positive (Fin 2) :=
  accessibilityOperator (checkerFormula data.scalar) (OrdinaryArithmeticQuotient.certificateGraph data.positive)

def multisetOperator (data : Data) : Positive (Fin 2) :=
  accessibilityOperator (checkerFormula data.multiset) (OrdinaryArithmeticQuotient.certificateGraph data.direct)

def sourceBody (data : Data) (context : Nat) : Positive (Fin 1) :=
  SourceEndpoint.substitutePositive ![numeral context,.var 0]
    (combinedOperator (scalarOperator data) (multisetOperator data))

def allTermsFormula (data : Data) (context : Nat) : Formula Empty :=
  allOne ((arithmeticEmbedding.onFormula ((checkerFormula data.scalar).subst
      ![numeral context,.var (.inr 0)])).imp
    (Positive.predicate (tagTerm false (.var (.inr (0 : Fin 1))))).formula)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentation
