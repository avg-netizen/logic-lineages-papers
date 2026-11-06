module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProductProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalCoprimeMultiple
open InternalCoprimeMultipleBoundedProof InternalCoprimeMultipleSupportProof InternalDivisibilityProductProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- The empty bounded family has positive common multiple one, coprime to every a. -/
theorem commonZero (a : OTerm α) (t : OTerm (α ⊕ Fin 1)) :
    Nonempty (Derivation body Gamma (commonMultiple a t z)) := by
  apply commonIntroduction a t z z (coprimeOne a)
  exact boundedZero _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBaseProof
