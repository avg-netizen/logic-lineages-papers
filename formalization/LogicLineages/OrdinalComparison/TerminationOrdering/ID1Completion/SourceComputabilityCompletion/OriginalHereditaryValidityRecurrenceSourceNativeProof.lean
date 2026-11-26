module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceMachineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRankProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceNativeProof
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrenceMachine
open OriginalHereditaryValidityRecurrenceSourceDecreaseProof
open OriginalHereditaryValidityRecurrenceSourceRankProof

/-- A proved node invariant constructs the finite native acceptance tree.
All rank induction is abstract and separate from these literal selectors. -/
theorem nativeAcceptedOfInvariant (source target member : Nat → Nat → Nat)
    (P : Frame → Prop)
    (hnode : ∀ frame, P frame → nodeCheckValue source target member frame.raw frame.parameter = 1)
    (happ : ∀ frame, P frame → tagValue frame.raw = 2 →
      P ⟨functionChildValue frame.raw,frame.parameter⟩ ∧
        P ⟨argumentChildValue frame.raw,frame.parameter⟩)
    (hlam : ∀ frame, P frame → tagValue frame.raw = 1 →
      P ⟨lambdaBodyValue frame.raw,childParameterValue frame.raw frame.parameter⟩)
    (frame : Frame) (htyped : P frame) :
    NativeAccepted source target member frame.raw frame.parameter := by
  have step : ∀ value parameter,
      (∀ child childParameter, payloadValue child < payloadValue value →
        P ⟨child,childParameter⟩ → NativeAccepted source target member child childParameter) →
      P ⟨value,parameter⟩ → NativeAccepted source target member value parameter := by
    intro value parameter ih ht
    have hn : nodeCheckValue source target member value parameter = 1 := hnode ⟨value,parameter⟩ ht
    by_cases ha : tagValue value = 2
    · have hp := happ ⟨value,parameter⟩ ht ha
      have hf : NativeAccepted source target member (functionChildValue value) parameter :=
        ih (functionChildValue value) parameter (functionPayloadLess value ha) hp.1
      have har : NativeAccepted source target member (argumentChildValue value) parameter :=
        ih (argumentChildValue value) parameter (argumentPayloadLess value ha) hp.2
      exact @NativeAccepted.application source target member value parameter hn ha hf har
    · by_cases hl : tagValue value = 1
      · have hp := hlam ⟨value,parameter⟩ ht hl
        have hb : NativeAccepted source target member
            (lambdaBodyValue value) (childParameterValue value parameter) :=
          ih (lambdaBodyValue value) (childParameterValue value parameter) (lambdaPayloadLess value hl) hp
        exact @NativeAccepted.lambda source target member value parameter hn hl hb
      · exact @NativeAccepted.other source target member value parameter hn ha hl
  have all : ∀ value parameter, P ⟨value,parameter⟩ → NativeAccepted source target member value parameter :=
    binaryRankInduction payloadValue (fun value parameter => P ⟨value,parameter⟩)
      (NativeAccepted source target member) step
  cases frame with
  | mk value parameter => exact all value parameter htyped

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceNativeProof
