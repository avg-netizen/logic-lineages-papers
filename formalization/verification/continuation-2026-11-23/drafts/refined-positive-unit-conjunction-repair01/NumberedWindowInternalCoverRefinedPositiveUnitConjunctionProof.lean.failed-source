module

public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedPositiveUnitConjunctionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination excludedMiddle)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A successor output of the actual normalized conjunction must be its
actual unit-acceptance output, with no calibration of either input. -/
theorem conjunctionUnitFromPositive {n : Nat} {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p q : Program n) (xs : Fin n → OTerm α) (value : OTerm α)
    (e : Nonempty (Derivation body Γ (programGraph (conjunction p q) (suc value) xs))) :
    Nonempty (Derivation body Γ (programGraph (conjunction p q) (suc z) xs)) := by
  let A := programGraph (conjunction p q) (suc z) xs
  obtain ⟨proof⟩ := e
  have yes : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have notUnit : Derivation body (A.not :: Γ) A.not := Derivation.hypothesis List.mem_cons_self
  have rejected := conjunctionReject p q xs ⟨notUnit⟩
  obtain ⟨impossible⟩ := valueUnique (conjunction p q) (suc value) z xs ⟨addHyp proof A.not⟩ rejected
  let no : Derivation body (A.not :: Γ) A := Derivation.explosion (sucNeZeroApply impossible)
  exact ⟨disjunctionElimination (excludedMiddle A) (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction no)⟩

#print axioms conjunctionUnitFromPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedPositiveUnitConjunctionProof
