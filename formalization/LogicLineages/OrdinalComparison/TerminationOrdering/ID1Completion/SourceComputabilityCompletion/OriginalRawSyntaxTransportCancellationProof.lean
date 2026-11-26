module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportRebuildFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCancellationProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportWeightProof OriginalRawSyntaxTransportSemanticProof
open OriginalRawSyntaxTransportRebuildFieldsProof OriginalRawSyntaxTransportCodeProof
open OriginalRawSyntaxTransportNativeRecurrenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Cancellation on the exact frozen domain: ALL raw naturals. Unknown tags
and malformed nil payloads are identity leaves. No typed decoding, source
validity, canonicalization, certificate, accessibility or computability is used. -/
 theorem semanticCancellation : ∀ (raw d k : Nat),
    semanticFold .erase d k (semanticFold .shift 0 k raw) = raw := by
  intro raw
  induction raw using Nat.strong_induction_on with
  | h raw ih =>
    intro d k
    rcases arityCases raw with h0 | h1 | h2
    · by_cases ht : tagValue raw = 0
      · have hp : raw = Nat.pair 0 (payloadValue raw) := by
          have hp := (Nat.pair_unpair raw).symm
          change raw = Nat.pair (tagValue raw) (payloadValue raw) at hp
          rw [ht] at hp
          exact hp
        rw [hp]
        exact variableCancellation d k (payloadValue raw)
      · have h1 : arityValue raw ≠ 1 := by omega
        have h2 : arityValue raw ≠ 2 := by omega
        have hs : semanticFold .shift 0 k raw = raw := by
          rw [semanticEquation, if_neg h1, if_neg h2]
          simp [leafValue, ht]
        rw [hs, semanticEquation, if_neg h1, if_neg h2]
        simp [leafValue, ht]
    · have hb := unaryChildBound raw h1
      let child := semanticFold .shift 0 (if tagValue raw = 1 then k + 1 else k) (firstValue raw)
      have hs : semanticFold .shift 0 k raw = rebuildValue .shift raw child 0 := by
        rw [semanticEquation, if_pos h1]
      have hf := rebuildFields raw child 0 (Or.inl h1)
      have ha : arityValue (rebuildValue .shift raw child 0) = 1 := hf.2.1.trans h1
      rw [hs, semanticEquation, if_pos ha, hf.2.2.1, hf.1]
      change rebuildValue .erase (rebuildValue .shift raw child 0)
        (semanticFold .erase d (if tagValue raw = 1 then k + 1 else k)
          (semanticFold .shift 0 (if tagValue raw = 1 then k + 1 else k) (firstValue raw))) 0 = raw
      rw [ih (firstValue raw) (by omega) d (if tagValue raw = 1 then k + 1 else k),
        hf.2.2.2.2, rebuildIdentityOne raw h1]
    · have hb := binaryChildrenBound raw h2
      let first := semanticFold .shift 0 k (firstValue raw)
      let second := semanticFold .shift 0 k (secondValue raw)
      have h1 : arityValue raw ≠ 1 := by omega
      have hs : semanticFold .shift 0 k raw = rebuildValue .shift raw first second := by
        rw [semanticEquation, if_neg h1, if_pos h2]
      have hf := rebuildFields raw first second (Or.inr h2)
      have ha : arityValue (rebuildValue .shift raw first second) = 2 := hf.2.1.trans h2
      have hn : arityValue (rebuildValue .shift raw first second) ≠ 1 := by omega
      rw [hs, semanticEquation, if_neg hn, if_pos ha, hf.2.2.1, hf.2.2.2.1 h2]
      change rebuildValue .erase (rebuildValue .shift raw first second)
        (semanticFold .erase d k (semanticFold .shift 0 k (firstValue raw)))
        (semanticFold .erase d k (semanticFold .shift 0 k (secondValue raw))) = raw
      rw [ih (firstValue raw) (by omega) d k, ih (secondValue raw) (by omega) d k,
        hf.2.2.2.2, rebuildIdentityTwo raw h2]

 theorem actualRawSyntaxNativeCancellation : OriginalRawSyntaxTransportTargets.ActualRawSyntaxNativeCancellation := by
  intro d k raw
  rw [eraseEvaluation]
  change foldValue .erase d k (evaluate shiftRaw (List.Vector.ofFn ![k,raw])) = raw
  rw [shiftEvaluation, foldSemantic, foldSemantic]
  exact semanticCancellation raw d k

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCancellationProof
