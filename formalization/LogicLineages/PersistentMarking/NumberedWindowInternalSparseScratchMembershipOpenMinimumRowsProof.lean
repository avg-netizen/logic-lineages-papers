module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMinimumRowsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseOrderedMinimum (minimumStep scratchMinimum)
open NumberedWindowInternalSparseOrderedMinimumOpenChecks (exact_OpenScratchMinimumCons)
open NumberedWindowInternalSparseScratchMembershipTargets
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual minimum at nil has no successful witness. Not even the
actual value zero is inserted by the membership antecedent. -/
theorem minimumNil (k : OTerm α) :
    Nonempty (Derivation body Γ (selectedOccurs z k)) := by
  let A := unary scratchMinimum (suc k) z
  let Δ := A :: Γ
  let empty : Fin 0 → OTerm α := Fin.elim0
  have input : Nonempty (Derivation body Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result := nilRecover (constantZero 0) minimumStep (suc k) empty input
  obtain ⟨contradiction⟩ := valueUnique (constantZero 0) (suc k) z empty result
    (zeroConstantValue empty)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply contradiction))⟩

/-- One actual cons induction step, using the accepted same-head or
same-tail minimum disjunction and genuine membership introductions. -/
theorem minimumCons (code h tail k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h tail)))
    (inherited : Nonempty (Derivation body Γ (selectedOccurs tail k))) :
    Nonempty (Derivation body Γ (selectedOccurs code k)) := by
  let A := unary scratchMinimum (suc k) code
  let L := eqn k h
  let R := unary scratchMinimum (suc k) tail
  let Δ := A :: Γ
  obtain ⟨c⟩ := cell
  obtain ⟨ih⟩ := inherited
  obtain ⟨step⟩ := exact_OpenScratchMinimumCons body α Δ code h tail k
  have split := Derivation.implicationElimination step
    (Derivation.conjunctionIntroduction (addHyp c A) (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨left⟩ := headMember (body := body) (Γ := L :: Δ) code h tail k
    ⟨addHyp (addHyp c A) L⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  have already : Derivation body (R :: Δ) (memberGraph tail k) :=
    Derivation.implicationElimination (addHyp (addHyp ih A) R) (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨right⟩ := tailMember (body := body) (Γ := R :: Δ) code h tail k
    ⟨addHyp (addHyp c A) R⟩ ⟨already⟩
  have actual := disjunctionElimination split
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)
  exact ⟨Derivation.implicationIntroduction actual⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMinimumRowsProof
