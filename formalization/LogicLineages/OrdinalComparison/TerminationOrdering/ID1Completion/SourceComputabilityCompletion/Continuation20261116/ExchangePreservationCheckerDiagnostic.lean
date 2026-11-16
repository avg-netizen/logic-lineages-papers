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
theorem leftThree : iterateValue signature member window 3 (initialValue leftRequest) contextNumber = Nat.pair 1 0 := by
  change transitionValue signature member window
    (transitionValue signature member window
      (transitionValue signature member window (initialValue leftRequest) contextNumber) contextNumber)
    contextNumber = Nat.pair 1 0
  simp [iterateValue,transitionValue,OriginalTypedDecoder.transitionValue,
    OriginalTypedDecoder.expandValue,guardValue,signature,member,window,contextMemberValue,
    headWindowValue,contextNumber,context,types,leftRequest,rightRequest,leftCode,rightCode,
    codeNumber,headNumber,typeNumber,typesNumber,initialValue,termRequestValue,
    OriginalTypedDecoder.argumentsRequestValue,OriginalTypedDecoder.requestMode,
    OriginalTypedDecoder.requestGamma,OriginalTypedDecoder.requestType,requestRaw,
    NumberedNumericDecoding.decodeHeadNumber,NumberedNumericDecoding.headParse,
    NumberedNumericDecoding.decodeType,
    NumberedAuxiliaryDecoding.decodeHead,NumberedFiniteUniverse.HeadInWindow,
    NumberedFiniteUniverse.RankedCovered,Source.SourceMarkedSyntax.headArguments,
    Source.SourceMarkedSyntax.headResult,InternalStructuralEndpointGuard.membershipValue,
    Nat.unpair_pair, (show Nat.pair 0 0 = 0 from rfl),
    (show Nat.pair 1 0 = 2 from rfl)]
theorem rightOne : transitionValue signature member window (initialValue rightRequest) contextNumber = 0 := by
  simp [iterateValue,transitionValue,OriginalTypedDecoder.transitionValue,
    OriginalTypedDecoder.expandValue,guardValue,signature,member,window,contextMemberValue,
    headWindowValue,contextNumber,context,types,leftRequest,rightRequest,leftCode,rightCode,
    codeNumber,headNumber,typeNumber,typesNumber,initialValue,termRequestValue,
    OriginalTypedDecoder.argumentsRequestValue,OriginalTypedDecoder.requestMode,
    OriginalTypedDecoder.requestGamma,OriginalTypedDecoder.requestType,requestRaw,
    NumberedNumericDecoding.decodeHeadNumber,NumberedNumericDecoding.headParse,
    NumberedNumericDecoding.decodeType,
    NumberedAuxiliaryDecoding.decodeHead,NumberedFiniteUniverse.HeadInWindow,
    NumberedFiniteUniverse.RankedCovered,Source.SourceMarkedSyntax.headArguments,
    Source.SourceMarkedSyntax.headResult,InternalStructuralEndpointGuard.membershipValue,
    Nat.unpair_pair, (show Nat.pair 0 0 = 0 from rfl),
    (show Nat.pair 1 0 = 2 from rfl)]
theorem leftFuelLarge : 3 ≤ requestRaw leftRequest + 1 := by
  simp only [leftRequest,termRequestValue,requestRaw,Nat.unpair_pair]
  simp [leftCode,codeNumber,headNumber,typeNumber,typesNumber,Nat.pair]
/-- Full original checkValue, exact raw+1 fuel; the remaining fuel is discharged
by the already-paid empty-state iteration law, not by native reflection. -/
theorem sourceAccepts : checkValue signature member window leftRequest contextNumber = 1 := by
  unfold checkValue
  have hf := leftFuelLarge
  have hn : requestRaw leftRequest + 1 = 3 + (requestRaw leftRequest + 1 - 3) := by omega
  rw [hn,iterateAdd,leftThree,emptyIteration]
  simp [finishedValue,Nat.unpair_pair]
/-- Full original target checkValue rejects after one step and stays failed. -/
theorem targetRejects : checkValue signature member window rightRequest contextNumber = 0 := by
  unfold checkValue
  rw [iterateSuccStart,rightOne,failedIteration]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationCheckerDiagnostic
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationCheckerDiagnostic
