module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalTagArithmeticSyntaxProof
open InternalCoprimeMultiple
/-- Object-calculus PA theorem for an arbitrary internal bound and arbitrary
positive term-defined modulus family; no external finite-length parameter. -/
def ActualBoundedCoprimeMultiple : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (m n : OTerm α) (t : OTerm (α ⊕ Fin 1)),
  Nonempty (Derivation body [] ((coprimeBelow (suc m) t n).imp (commonMultiple (suc m) t n)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleTargets
