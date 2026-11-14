module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportRebuildFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Proof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalRawSyntaxTransportWeightProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)

theorem dependencyValue (raw param : Nat) :
    evaluate dependency (List.Vector.ofFn ![raw,param]) = numbersNumber (rawChildren raw) := by
  change evaluate ArgumentEntriesChildren.children (List.Vector.ofFn ![raw]) = _
  rw [ArgumentEntriesChildren.NativeProof.childrenValue]
  unfold rawChildren
  split_ifs <;> rfl

theorem rawDecrease (raw child : Nat) (hc : child ∈ rawChildren raw) : child < raw := by
  rcases OriginalRawSyntaxTransportRebuildFieldsProof.arityCases raw with h0 | h1 | h2
  · simp [rawChildren,h0] at hc
  · have hb := unaryChildBound raw h1
    have he : child = firstValue raw := by simpa [rawChildren,h1] using hc
    omega
  · have hb := binaryChildrenBound raw h2
    have he : child = firstValue raw ∨ child = secondValue raw := by simpa [rawChildren,h2] using hc
    rcases he with he | he <;> omega

theorem rawDependency : Targets.RawDependency := ⟨dependencyValue,rawDecrease⟩

theorem childrenImage (n : Nat) (c : Code (Fin n)) :
    rawChildren (codeNumber c) = (NumberedSyntaxBoundsPrimrecSupportProof.children c).map codeNumber := by
  cases c <;> simp [rawChildren,arityValue,firstValue,secondValue,tagValue,payloadValue,
    codeNumber,Nat.unpair_pair,NumberedSyntaxBoundsPrimrecSupportProof.children]

theorem flattenImage (n : Nat) (nodes : List (Code (Fin n))) :
    (nodes.map codeNumber).flatMap rawChildren =
      (nodes.flatMap NumberedSyntaxBoundsPrimrecSupportProof.children).map codeNumber := by
  induction nodes with
  | nil => rfl
  | cons c nodes ih =>
    simp only [List.map_cons,List.flatMap_cons,childrenImage,List.map_append,ih]

theorem frontierImage (n : Nat) (seed : Code (Fin n)) (depth : Nat) :
    Nat.rec [codeNumber seed] (fun _ nodes => nodes.flatMap rawChildren) depth =
      (originalFrontier seed depth).map codeNumber := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (Nat.rec [codeNumber seed] (fun _ nodes => nodes.flatMap rawChildren) depth).flatMap rawChildren = _
    rw [ih,flattenImage]
    rfl

theorem validFrontier : Targets.ValidFrontier := by
  intro n seed depth param
  rw [ExchangeFrontier.NativeProof.nativeBindList dependency (fun raw _ => rawChildren raw) dependencyValue]
  rw [frontierImage]

theorem rankBound (n : Nat) (seed : Code (Fin n)) (depth : Nat) (child : Code (Fin n))
    (hc : child ∈ originalFrontier seed depth) : codeNumber child + depth ≤ codeNumber seed := by
  induction depth generalizing child with
  | zero =>
    have he : child = seed := by simpa [originalFrontier] using hc
    subst child
    exact Nat.le_refl _
  | succ depth ih =>
    change child ∈ (originalFrontier seed depth).flatMap NumberedSyntaxBoundsPrimrecSupportProof.children at hc
    obtain ⟨parent,hp,hchild⟩ := List.mem_flatMap.mp hc
    have hb := ih parent hp
    have hd := NumberedSyntaxBoundsPrimrecSupportProof.childrenDecrease n parent child hchild
    omega

theorem originalRankExhaustion : Targets.OriginalRankExhaustion := by
  intro n seed
  refine ⟨rankBound n seed,?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro child hc
  have hb := rankBound n seed _ child hc
  omega
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Proof
