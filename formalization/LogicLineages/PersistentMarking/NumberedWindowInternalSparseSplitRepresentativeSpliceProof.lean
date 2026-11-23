module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentAdjacentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSplitRepresentativeSpliceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityTransportProof (moveSource)
open NumberedWindowInternalSparsePositiveTransitivityChecks (exact_OpenPositiveTransitivity)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A genuine object-level equality of middle classes splices literal
positive paths at the arbitrary physical raw/least programs passed here.
The two path witnesses are preserved as the actual input to checked
positive transitivity, not rerun on host numerals. -/
theorem splice (raw : Program 5) (L : Program 3)
    (ctx ty x c a b d y : OTerm α)
    (middle : Nonempty (Derivation B Γ (eqn b a)))
    (left : Nonempty (Derivation B Γ (positiveAt raw L ctx ty x c a)))
    (right : Nonempty (Derivation B Γ (positiveAt raw L ctx ty b d y))) :
    Nonempty (Derivation B Γ (supplied raw L ctx ty x y)) := by
  obtain ⟨next⟩ := moveSource raw L ctx ty b a d y middle right
  obtain ⟨prev⟩ := left
  exact closedApply (exact_OpenPositiveTransitivity B raw L α ctx ty x c a d y)
    ⟨Derivation.conjunctionIntroduction prev next⟩

/-- The middle representatives may differ. The single local missing
bridge is precisely the report that the suffix representative applied to
the *same raw argument* also denotes the prefix application class.
The two original application reports are retained in the interface; in
the final step functionality is used only at the suffix representative,
never at unequal raw function terms. -/
theorem splitRepresentative (raw : Program 5) (L : Program 3)
    (ctx dom cod f g arg x c a b d y : OTerm α)
    (_firstLeast : Nonempty (Derivation B Γ
      (programGraph L (suc a) ![ctx,cod,auxiliaryTerm dom cod f arg])))
    (secondLeast : Nonempty (Derivation B Γ
      (programGraph L (suc b) ![ctx,cod,auxiliaryTerm dom cod g arg])))
    (crossLeast : Nonempty (Derivation B Γ
      (programGraph L (suc a) ![ctx,cod,auxiliaryTerm dom cod g arg])))
    (left : Nonempty (Derivation B Γ (positiveAt raw L ctx cod x c a)))
    (right : Nonempty (Derivation B Γ (positiveAt raw L ctx cod b d y))) :
    Nonempty (Derivation B Γ (supplied raw L ctx cod x y)) := by
  obtain ⟨e⟩ := valueUnique L (suc b) (suc a)
    ![ctx,cod,auxiliaryTerm dom cod g arg] secondLeast crossLeast
  exact splice raw L ctx cod x c a b d y ⟨cancelSuc e⟩ left right

#print axioms splice
#print axioms splitRepresentative
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSplitRepresentativeSpliceProof
