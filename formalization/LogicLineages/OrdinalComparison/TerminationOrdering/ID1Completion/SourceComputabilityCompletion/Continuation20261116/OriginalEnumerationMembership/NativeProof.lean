module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open Continuation20261115
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem memberEncoding {alpha : Type} [Encodable alpha] (x : alpha) (xs : List alpha) :
    Encodable.encode x ∈ xs.map Encodable.encode ↔ x ∈ xs := by
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := List.mem_map.mp h
    cases Encodable.encode_injective he
    exact hy
  · intro h
    exact List.mem_map.mpr ⟨x,h,rfl⟩

theorem containsEncoding {n : Nat} (c : Code (Fin n)) (xs : List (Code (Fin n))) :
    evaluate contains (ofFn ![Encodable.encode xs,codeNumber c]) = 1 ↔ c ∈ xs := by
  rw [TwoSol20261113.CalibratedPrimary.MembershipNativeProof.actualContainsNative,
    OriginalTypeListsEnumeration.CodecProof.listEncoding,numbersRoundTrip]
  change (decide (Encodable.encode c ∈ xs.map Encodable.encode)).toNat = 1 ↔ c ∈ xs
  by_cases h : c ∈ xs
  · have hm := (memberEncoding c xs).mpr h
    simp [h,hm]
  · have hm : Encodable.encode c ∉ xs.map Encodable.encode := fun hm => h ((memberEncoding c xs).mp hm)
    simp [h,hm]

theorem nativeOriginal : Targets.NativeOriginal := by
  intro n S H labels tupleBound variableBound fuel c
  rw [OriginalEnumerationRecursion.OriginalProof.nativeOriginal n (S,(H,(labels,tupleBound))) variableBound fuel]
  rw [containsEncoding]
  exact NumberedAuxiliaryEnumerationSupportProof.codeEnumeration (Fin n) S H labels tupleBound variableBound fuel c
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NativeProof
