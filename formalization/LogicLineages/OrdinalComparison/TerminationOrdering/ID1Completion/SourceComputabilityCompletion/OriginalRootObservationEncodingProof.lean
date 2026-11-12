module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationEncodingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationEncodingProof
open Source NumberedLeastCodeRepresentative NumberedHereditaryView OriginalRootObservation
open NumberedLeastCodeRepresentativeSupportProof (typeNumberInjective)
open OriginalNumericListSortNativeProof (numbersInjective)

theorem typedInjective : Function.Injective typedNumber := by
 intro x y h
 obtain ⟨t,a⟩ := x
 obtain ⟨u,b⟩ := y
 have hp := Nat.pair_eq_pair.mp h
 exact Prod.ext (typeNumberInjective hp.1) hp.2

theorem classInjective (n : Nat) : Function.Injective (@classNumber n) := by
 intro x y h
 cases x <;> cases y <;> simp_all [classNumber,Fin.val_inj] <;> omega

theorem multisetInjective : Function.Injective multisetNumber := by
 intro x y h
 have hs := numbersInjective h
 have hm := congrArg (fun xs : List Nat => (xs : Multiset Nat)) hs
 simp only [Multiset.sort_eq] at hm
 exact Multiset.map_injective typedInjective hm

theorem extrasInjective : Function.Injective (fun xs : List (Ty × Nat) =>
 NumberedMultisetNumeric.numbersNumber (xs.map typedNumber)) := by
 intro x y h
 exact (List.map_injective_iff.mpr typedInjective) (numbersInjective h)

theorem signatureInjective (n : Nat) : Function.Injective (@signatureNumber n) := by
 intro x y h
 cases x <;> cases y <;>
   simp_all [signatureNumber,Nat.pair_eq_pair,typeNumberInjective.eq_iff,
     typedInjective.eq_iff,(classInjective n).eq_iff,multisetInjective.eq_iff,
     extrasInjective.eq_iff]

theorem exactEncoding : OriginalRootObservationEncodingTargets.ExactEncoding :=
 ⟨typedInjective,multisetInjective,signatureInjective⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationEncodingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationEncodingProof
