module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSemanticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeSemanticProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportWeightProof
def stateStep (state : State) : State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | frame :: rest =>
      let tag := (Nat.unpair frame).1
      let p := (Nat.unpair frame).2
      if tag = 0 then
        let d := (Nat.unpair p).1
        let k := (Nat.unpair (Nat.unpair p).2).1
        let raw := (Nat.unpair (Nat.unpair p).2).2
        if arityValue raw = 1 then
          let childCutoff := if tagValue raw = 1 then k + 1 else k
          ⟨1, visitValue d childCutoff (firstValue raw) :: finishValue raw :: rest, state.results⟩
        else if arityValue raw = 2 then
          ⟨1, visitValue d k (firstValue raw) :: visitValue d k (secondValue raw) :: finishValue raw :: rest, state.results⟩
        else ⟨1, rest, 1 :: state.results⟩
      else if tag = 1 then
        if arityValue p = 1 then
          match state.results with
          | first :: results => ⟨1, rest, OriginalStructuralNodeSize.rebuildValue p first 0 :: results⟩
          | _ => failedState
        else if arityValue p = 2 then
          match state.results with
          | second :: first :: results => ⟨1, rest, OriginalStructuralNodeSize.rebuildValue p first second :: results⟩
          | _ => failedState
        else failedState
      else failedState
  else failedState

/-- Independent native recursion on the ORIGINAL raw numeric tree. It does not
mention the Program AST, any machine run, a fuel value, source typing or C/I. -/
def semanticFold (d k raw : Nat) : Nat :=
  if h1 : arityValue raw = 1 then
    OriginalStructuralNodeSize.rebuildValue raw
      (semanticFold d (if tagValue raw = 1 then k + 1 else k) (firstValue raw)) 0
  else if h2 : arityValue raw = 2 then
    OriginalStructuralNodeSize.rebuildValue raw (semanticFold d k (firstValue raw)) (semanticFold d k (secondValue raw))
  else 1
termination_by raw
decreasing_by
  · have hb := unaryChildBound raw h1
    omega
  · have hb := binaryChildrenBound raw h2
    omega
  · have hb := binaryChildrenBound raw h2
    omega

 theorem semanticEquation (d k raw : Nat) :
    semanticFold d k raw =
      if arityValue raw = 1 then OriginalStructuralNodeSize.rebuildValue raw
        (semanticFold d (if tagValue raw = 1 then k + 1 else k) (firstValue raw)) 0
      else if arityValue raw = 2 then OriginalStructuralNodeSize.rebuildValue raw
        (semanticFold d k (firstValue raw)) (semanticFold d k (secondValue raw))
      else 1 := by
  rw [semanticFold]
  split_ifs <;> rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeSemanticProof
