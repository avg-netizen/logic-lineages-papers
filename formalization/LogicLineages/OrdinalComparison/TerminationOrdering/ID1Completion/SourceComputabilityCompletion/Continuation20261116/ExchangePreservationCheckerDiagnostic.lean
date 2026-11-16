module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationDiagnostic
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationCheckerDiagnostic
open Source NumberedLeastCodeRepresentative
open ExchangePreservationDiagnostic (arity types leftCode rightCode)
open OriginalUniverseDecoder
open OriginalUniverseDecoderEncodedProof
open OriginalTypedDecoder (termRequestValue initialValue finishedValue requestRaw)
def signature (head : Nat) : Nat := if head = 0 then 1 else 0
def context : OrdinaryArithmeticQuotient.Context 0 := (([],types),fun i => Fin.elim0 i)
def contextNumber : Nat := Encodable.encode context
def member : Nat → Nat → Nat := contextMemberValue 0
def window : Nat → Nat → Nat := headWindowValue 0 arity
def leftRequest : Nat := termRequestValue (Encodable.encode ([] : List Ty)) 0 (codeNumber leftCode)
def rightRequest : Nat := termRequestValue (Encodable.encode ([] : List Ty)) 0 (codeNumber rightCode)
/-- Only THREE original transitions are reduced, not the enormous raw+1 fuel. -/
theorem leftThree : iterateValue signature member window 3 (initialValue leftRequest) contextNumber = Nat.pair 1 0 := by decide
theorem rightOne : transitionValue signature member window (initialValue rightRequest) contextNumber = 0 := by decide
theorem leftFuelLarge : 3 ≤ requestRaw leftRequest + 1 := by decide
/-- Full original checkValue, exact raw+1 fuel; the remaining fuel is discharged
by the already-paid empty-state iteration law, not by native reflection. -/
theorem sourceAccepts : checkValue signature member window leftRequest contextNumber = 1 := by
  unfold checkValue
  have hf := leftFuelLarge
  have hn : requestRaw leftRequest + 1 = 3 + (requestRaw leftRequest + 1 - 3) := by omega
  rw [hn,iterateAdd,leftThree,emptyIteration]
  rfl
/-- Full original target checkValue rejects after one step and stays failed. -/
theorem targetRejects : checkValue signature member window rightRequest contextNumber = 0 := by
  unfold checkValue
  rw [iterateSuccStart,rightOne,failedIteration]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationCheckerDiagnostic
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationCheckerDiagnostic
