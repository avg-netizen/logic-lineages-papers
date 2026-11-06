module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariant
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof PositiveArithmeticPredicateSubstitution InternalCalculus

/-- A tag selects the payload of an arbitrary first-order invariant.
The invariant itself is NOT required to be positive in the inductive predicate. -/
def branch {α : Type} (odd : Bool) (phi : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  allOne ((arithmeticEmbedding.onFormula
    ((.var (.inl (.inr (0 : Fin 1))) : OrdinaryArithmetic.Term ((α ⊕ Fin 1) ⊕ Fin 1)).equal
      (tagTerm odd (.var (.inr 0))))).imp (liftPredicateFormula phi))

def tagged {α : Type} (scalar multiset : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  branch false scalar ⊓ branch true multiset

/-- The literal antecedent of the existing one-body leastness schema. -/
def closurePremise {α : Type} (body : Positive (Fin 1))
    (theta : Formula (α ⊕ Fin 1)) : Formula α :=
  allOne ((replacedBody body theta).imp theta)

/-- The existing finite-S formula with context and type as parameters and
an original context-carrying Object code as its final argument. -/
def window (data : JointGammaComputability.Data) (S : List Ty) : Formula (Fin 2 ⊕ Fin 1) :=
  (SourceFiniteComputabilityFormula.windowFormula (JointGammaComputability.formula data) S).relabel
    ![.inl 0,.inl 1,.inr 0]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariant
