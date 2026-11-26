module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSemanticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportRebuildFieldsProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportWeightProof OriginalRawSyntaxTransportSemanticProof

 theorem arityCases (raw : Nat) : arityValue raw = 0 ∨ arityValue raw = 1 ∨ arityValue raw = 2 := by
  unfold arityValue
  split_ifs <;> simp

 theorem structuralTags (raw : Nat) (h : arityValue raw = 1 ∨ arityValue raw = 2) :
    tagValue raw = 1 ∨ tagValue raw = 2 ∨ tagValue raw = 4 ∨ tagValue raw = 5 ∨ tagValue raw = 7 := by
  rcases h with h1 | h2
  · rcases unaryTags raw h1 with ht | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inr (Or.inl ht))
  · rcases binaryTags raw h2 with ht | ht | ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ht)))

/-- Reconstruction retains all original metadata. The branch laws are total
arithmetic facts about arbitrary raw fields, not typed source propositions. -/
 theorem rebuildFields (raw first second : Nat) (h : arityValue raw = 1 ∨ arityValue raw = 2) :
    tagValue (rebuildValue .shift raw first second) = tagValue raw ∧
    arityValue (rebuildValue .shift raw first second) = arityValue raw ∧
    firstValue (rebuildValue .shift raw first second) = first ∧
    (arityValue raw = 2 → secondValue (rebuildValue .shift raw first second) = second) ∧
    (∀ a b : Nat, rebuildValue .erase (rebuildValue .shift raw first second) a b = rebuildValue .shift raw a b) := by
  rcases structuralTags raw h with ht | ht | ht | ht | ht <;>
    simp only [tagValue] at ht <;>
    simp [rebuildValue, arityValue, tagValue, payloadValue, firstValue, secondValue, ht]

 theorem rebuildIdentityOne (raw : Nat) (h : arityValue raw = 1) :
    rebuildValue .shift raw (firstValue raw) 0 = raw := by
  calc
    rebuildValue .shift raw (firstValue raw) 0 = Nat.pair (tagValue raw) (payloadValue raw) := by
      rcases unaryTags raw h with ht | ht <;>
        simp only [tagValue] at ht <;>
        simp [rebuildValue, firstValue, tagValue, payloadValue, ht]
    _ = raw := Nat.pair_unpair raw

 theorem rebuildIdentityTwo (raw : Nat) (h : arityValue raw = 2) :
    rebuildValue .shift raw (firstValue raw) (secondValue raw) = raw := by
  calc
    rebuildValue .shift raw (firstValue raw) (secondValue raw) = Nat.pair (tagValue raw) (payloadValue raw) := by
      rcases binaryTags raw h with ht | ht | ht <;>
        simp only [tagValue] at ht <;>
        simp [rebuildValue, firstValue, secondValue, tagValue, payloadValue, ht]
    _ = raw := Nat.pair_unpair raw

 theorem semanticVariable (mode : Mode) (d k index : Nat) :
    semanticFold mode d k (Nat.pair 0 index) = leafValue mode d k (Nat.pair 0 index) := by
  rw [semanticEquation]
  simp [arityValue, tagValue]

 theorem variableCancellation (d k index : Nat) :
    semanticFold .erase d k (semanticFold .shift 0 k (Nat.pair 0 index)) = Nat.pair 0 index := by
  rw [semanticVariable]
  simp only [leafValue, tagValue, payloadValue, Nat.unpair_pair, if_true]
  by_cases h : index < k
  · rw [if_pos h, semanticVariable]
    simp [leafValue, tagValue, payloadValue, h]
  · rw [if_neg h, semanticVariable]
    have hb : ¬ index + 1 < k := by omega
    have he : index + 1 ≠ k := by omega
    simp [leafValue, tagValue, payloadValue, hb, he]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportRebuildFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportRebuildFieldsProof
