module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectMultisetTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetSound
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticAllContextTargets
open NumberedWindowArithmeticAllContextChecks
open NumberedWindowArithmeticDirectMultisetBits NumberedWindowArithmeticDirectMultisetTargets

theorem typed : ExactTypedAddressListBit := by
  intro S K xs hk
  simp only [typedAddressListBit,List.all_eq_true,TypedAddressList]
  constructor
  · intro h a ha
    exact (exact_AdmittedAddressBit S K a hk).mp (h a ha)
  · intro h a ha
    exact (exact_AdmittedAddressBit S K a hk).mpr (h a ha)

theorem insertion {S K removed e} (hk : DecisionSourceUniverse.Closed K)
    (h : insertionBit S K removed e = true) :
    e.dominator ∈ removed ∧ AddressPositive S K e.dominator e.target := by
  simp only [insertionBit,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1,(exact_AddressPositivePath S K e.dominator e.target hk).mp ⟨e.certificate,h.2⟩⟩

theorem supplied : SuppliedDirectMultisetSound := by
  intro S K source target w hk h
  simp only [directMultisetBit,Bool.and_eq_true,typed S K source hk,typed S K target hk,
    decide_eq_true_eq,Bool.not_eq_true',List.isEmpty_eq_false_iff,List.all_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hs,ht⟩,hSrc⟩,hDst⟩,hne⟩,hInserts⟩
  refine ⟨hs,ht,w.kept,w.removed,w.inserted.map InsertedOccurrence.target,hSrc,hDst,hne,?_⟩
  intro a ha
  obtain ⟨e,he,hTarget⟩ := List.mem_map.mp ha
  obtain ⟨hDom,hPath⟩ := insertion hk (hInserts e he)
  rw [hTarget] at hPath
  exact ⟨e.dominator,hDom,hPath⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetSound
