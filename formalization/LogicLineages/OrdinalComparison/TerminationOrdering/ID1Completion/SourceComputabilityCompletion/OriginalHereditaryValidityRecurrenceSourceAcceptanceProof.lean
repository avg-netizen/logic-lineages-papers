module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceDescendantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceLeavesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceNumericProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceAcceptanceProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrence OriginalHereditaryValidityRecurrenceMachine
open OriginalHereditaryValidityRecurrenceSourceDescendantProof
open OriginalHereditaryValidityRecurrenceSourceLeavesProof
open OriginalHereditaryValidityRecurrenceSourceNativeProof
open OriginalHereditaryValidityRecurrenceNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The existing bounded machine accepts every typed-window frame. Every
finite acceptance-tree obligation is discharged by the original decoded
window, at the literal child frame's own parameter. -/
theorem typedValidator (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (context : Nat) (frame : Frame)
    (htyped : TypedWindowFrame n arity context frame) :
    validatorValue
      (fun value parameter => evaluate data.oldSource (List.Vector.ofFn ![value,parameter]))
      (fun value parameter => evaluate data.oldTarget (List.Vector.ofFn ![value,parameter]))
      (fun value parameter => evaluate data.member (List.Vector.ofFn ![value,parameter]))
      frame.raw frame.parameter = 1 := by
  let source : Nat → Nat → Nat :=
    fun value parameter => evaluate data.oldSource (List.Vector.ofFn ![value,parameter])
  let target : Nat → Nat → Nat :=
    fun value parameter => evaluate data.oldTarget (List.Vector.ofFn ![value,parameter])
  let member : Nat → Nat → Nat :=
    fun value parameter => evaluate data.member (List.Vector.ofFn ![value,parameter])
  have hn : ∀ current, TypedWindowFrame n arity context current →
      nodeCheckValue source target member current.raw current.parameter = 1 := by
    intro current ht
    exact typedNode n arity data hc context current ht
  have ha : ∀ current, TypedWindowFrame n arity context current → tagValue current.raw = 2 →
      TypedWindowFrame n arity context ⟨functionChildValue current.raw,current.parameter⟩ ∧
        TypedWindowFrame n arity context ⟨argumentChildValue current.raw,current.parameter⟩ := by
    intro current ht htag
    exact applicationChildren ht htag
  have hl : ∀ current, TypedWindowFrame n arity context current → tagValue current.raw = 1 →
      TypedWindowFrame n arity context
        ⟨lambdaBodyValue current.raw,childParameterValue current.raw current.parameter⟩ := by
    intro current ht htag
    exact lambdaChild ht htag
  have ht : NativeAccepted source target member frame.raw frame.parameter :=
    nativeAcceptedOfInvariant source target member (TypedWindowFrame n arity context) hn ha hl frame htyped
  exact (validatorNativeAcceptance source target member frame.raw frame.parameter).mpr ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceAcceptanceProof
