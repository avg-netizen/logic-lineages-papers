module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAgreementBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementArithmeticProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans)
open ID1Completion.InternalAdditionLawsProof (congAddLeft)
open ID1Completion.InternalAdditionCancellationProof (leftCancellation)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendProof (exact_LiteralOpenCountAppend)
open NumberedWindowInternalLiteralCountAllQueriesTargets (agreement)
open NumberedWindowInternalLiteralCountAgreementBindingProof (agreementApply)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Actual query congruence for the same kept (front) code. All five
entryCount outputs and both append outputs are genuine graph reports. -/
theorem commonPrefixCongruenceAt (front left right joinedL joinedR key cp cl cr ctl ctr : OTerm α)
    (apl : Nonempty (Derivation B Γ (appended front left joinedL)))
    (apr : Nonempty (Derivation B Γ (appended front right joinedR)))
    (p : Nonempty (Derivation B Γ (counted front key cp)))
    (l : Nonempty (Derivation B Γ (counted left key cl)))
    (r : Nonempty (Derivation B Γ (counted right key cr)))
    (ol : Nonempty (Derivation B Γ (counted joinedL key ctl)))
    (orr : Nonempty (Derivation B Γ (counted joinedR key ctr)))
    (agree : Nonempty (Derivation B Γ (agreement left right))) :
    Nonempty (Derivation B Γ (eqn ctl ctr)) := by
  obtain ⟨a⟩ := exact_LiteralOpenCountAppend front left key joinedL cp cl ctl apl p l ol
  obtain ⟨b⟩ := exact_LiteralOpenCountAppend front right key joinedR cp cr ctr apr p r orr
  obtain ⟨c⟩ := agreementApply left right key cl cr agree l r
  exact ⟨trans a (trans (congAddLeft cp c) (symm b))⟩

/-- Actual query cancellation for the same kept (front) code, with
integer-free internal arithmetic cancellation of the common Nat addend. -/
theorem commonPrefixCancellationAt (front left right joinedL joinedR key cp cl cr ctl ctr : OTerm α)
    (apl : Nonempty (Derivation B Γ (appended front left joinedL)))
    (apr : Nonempty (Derivation B Γ (appended front right joinedR)))
    (p : Nonempty (Derivation B Γ (counted front key cp)))
    (l : Nonempty (Derivation B Γ (counted left key cl)))
    (r : Nonempty (Derivation B Γ (counted right key cr)))
    (ol : Nonempty (Derivation B Γ (counted joinedL key ctl)))
    (orr : Nonempty (Derivation B Γ (counted joinedR key ctr)))
    (agree : Nonempty (Derivation B Γ (agreement joinedL joinedR))) :
    Nonempty (Derivation B Γ (eqn cl cr)) := by
  obtain ⟨a⟩ := exact_LiteralOpenCountAppend front left key joinedL cp cl ctl apl p l ol
  obtain ⟨b⟩ := exact_LiteralOpenCountAppend front right key joinedR cp cr ctr apr p r orr
  obtain ⟨c⟩ := agreementApply joinedL joinedR key ctl ctr agree ol orr
  exact ⟨Derivation.implicationElimination (leftCancellation cl cr cp) (trans (symm a) (trans c b))⟩

#print axioms commonPrefixCongruenceAt
#print axioms commonPrefixCancellationAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementArithmeticProof
