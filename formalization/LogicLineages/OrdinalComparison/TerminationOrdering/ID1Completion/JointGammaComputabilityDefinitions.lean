module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputability
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof SourceComputabilityFormulaProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original type recursion, on context-carrying objects. Arrow arguments
are restricted to the SAME Gamma; ground membership uses the existing even tag. -/
def Computable (n : Nat) (arity : Fin n → Nat) (P : Nat → Prop) (context : Nat) : Ty → Nat → Prop
  | .ground, x => JointGammaTyped.encodedTyped n arity context (typeNumber .ground) x ∧ P (tagNumber false x)
  | .arrow sigma tau, x =>
      JointGammaTyped.encodedTyped n arity context (typeNumber (.arrow sigma tau)) x ∧
      ∀ u : Nat, JointGammaDomain.sameContext x u → Computable n arity P context sigma u →
        ∃ z : Nat, JointGammaApplication.encodedApplication n arity context
          (typeNumber sigma) (typeNumber tau) x u z ∧ Computable n arity P context tau z

/-- Actual finite arithmetic checker Programs; no truth/closure fields. -/
structure Data where
  typed : Program 3
  guard : Program 2
  application : Program 6

def Calibrated (data : Data) (n : Nat) (arity : Fin n → Nat) : Prop :=
  (∀ v, evaluate data.typed v = JointGammaTyped.typedValue n arity v) ∧
  (∀ v, evaluate data.guard v = JointGammaDomain.guardValue v) ∧
  (∀ v, evaluate data.application v = JointGammaApplication.applicationValue n arity v)

def guardAt (p : Program 2) : language.Formula (Fin 2 ⊕ Fin 1) :=
  arithmeticEmbedding.onFormula ((SourcePresentation.checkerFormula p).subst
    ![.var (.inl 1),.var (.inr 0)])

/-- Literal finite recursion producing ordinary first-order invariant formulas.
The arrow antecedent may contain P negatively; this is NOT a new inductive operator. -/
def formula (data : Data) : Ty → language.Formula (Fin 2)
  | .ground => typedAt (JointGammaTyped.typedFormula data.typed) .ground ⊓
      (Positive.predicate (tagTerm false (.var 1))).formula
  | .arrow sigma tau => typedAt (JointGammaTyped.typedFormula data.typed) (.arrow sigma tau) ⊓
      allOne ((guardAt data.guard).imp
        (((formula data sigma).relabel ![.inl 0,.inr 0]).imp
          (existsOne (appAt (JointGammaApplication.applicationFormula data.application) sigma tau ⊓
            (formula data tau).relabel ![.inl (.inl 0),.inr 0]))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputability
