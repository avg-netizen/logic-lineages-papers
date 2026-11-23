module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectMultisetSound

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetComplete
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticAllContextTargets
open NumberedWindowArithmeticAllContextChecks
open NumberedWindowArithmeticDirectMultisetBits NumberedWindowArithmeticDirectMultisetTargets
open NumberedWindowArithmeticDirectMultisetSound

private theorem assemble {S K removed} (hk : DecisionSourceUniverse.Closed K) :
    ∀ added : List Nat, (∀ a ∈ added, ∃ b ∈ removed, AddressPositive S K b a) →
      ∃ es : List InsertedOccurrence, es.map InsertedOccurrence.target = added ∧
        es.all (insertionBit S K removed) = true := by
  intro added
  induction added with
  | nil => intro _; exact ⟨[],rfl,rfl⟩
  | cons a rest ih =>
    intro h
    obtain ⟨b,hb,hp⟩ := h a List.mem_cons_self
    obtain ⟨cert,hcert⟩ := (exact_AddressPositivePath S K b a hk).mpr hp
    obtain ⟨es,he,ht⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    let e : InsertedOccurrence := ⟨a,b,cert⟩
    have hHead : insertionBit S K removed e = true := by
      simp only [insertionBit,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨hb,hcert⟩
    refine ⟨e :: es,?_,?_⟩
    · simp [e,he]
    · exact Bool.and_eq_true_iff.mpr ⟨hHead,ht⟩

theorem complete {S K source target} (hk : DecisionSourceUniverse.Closed K)
    (h : AddressDirect S K source target) :
    ∃ w, directMultisetBit S K source target w = true := by
  obtain ⟨hs,ht,kept,removed,added,hSrc,hDst,hne,hDom⟩ := h
  obtain ⟨es,hMap,hInserts⟩ := assemble hk added hDom
  refine ⟨⟨kept,removed,es⟩,?_⟩
  simp only [directMultisetBit,Bool.and_eq_true,typed S K source hk,typed S K target hk,
    decide_eq_true_eq,Bool.not_eq_true',List.isEmpty_eq_false_iff]
  rw [hMap]
  exact ⟨⟨⟨⟨⟨hs,ht⟩,hSrc⟩,hDst⟩,hne⟩,hInserts⟩

theorem exactDirect : ExactCertifiedDirectMultiset := by
  intro S K source target hk
  exact ⟨fun ⟨w,h⟩ => supplied S K source target w hk h,complete hk⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetComplete
