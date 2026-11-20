import LogicLineages.PersistentMarking.NumberedWindowConstructorRawArgumentTargets
import LogicLineages.PersistentMarking.NumberedWindowConstructorStatMarkProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassChecks
import LogicLineages.PersistentMarking.NumberedWindowPreservationRawProof

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorRawArgumentProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextTargets
open NumberedWindowConstructorArgumentAddresses NumberedWindowArithmeticDirectMultisetTargets
open NumberedWindowConstructorRawArgumentTargets
open NumberedWindowConstructorStatMarkProof (slotCode)

theorem positive : RawStepPositiveAddresses := by
  intro S K Γ q r source target hk hq hr hRaw hSource hTarget
  have ht := (NumberedWindowPreservationRawProof.rawGuard hk hRaw _ hq).1
  have hr' : InWindow S K (finiteC Γ) q.type r := ht ▸ hr
  obtain ⟨i, hi, hEncodeSource⟩ := slotCode hSource
  obtain ⟨j, hj, hEncodeTarget⟩ := slotCode hTarget
  rw [ht] at hj hEncodeTarget
  let Q : WindowCarrier S K (finiteC Γ) q.type := ⟨q, hq⟩
  let R : WindowCarrier S K (finiteC Γ) q.type := ⟨r, hr'⟩
  exact ⟨Γ, q.type, i, j, classOf Q, classOf R, hEncodeSource, hEncodeTarget,
    ⟨Q, rfl, hi⟩, ⟨R, rfl, hj⟩, .one ⟨Q, R, rfl, rfl, hRaw⟩⟩

private theorem location {S K} (xs ys : NArgs) (h : RawArgsStep S K xs ys) :
    ∃ front suffix : List NTerm, ∃ before after : NTerm,
      xs.toList = front ++ before :: suffix ∧ ys.toList = front ++ after :: suffix ∧
        RawStep S K before after := by
  cases xs with
  | nil => cases h
  | cons q tail =>
    cases h with
    | first hRaw => exact ⟨[], tail.toList, _, _, rfl, rfl, hRaw⟩
    | later hTail =>
      obtain ⟨front, suffix, before, after, hSrc, hDst, hRaw⟩ := location tail _ hTail
      exact ⟨q :: front, suffix, before, after,
        by simp only [NArgs.toList, List.cons_append, hSrc],
        by simp only [NArgs.toList, List.cons_append, hDst], hRaw⟩
termination_by sizeOf xs

private theorem actualCode {S K Γ q} (hk : DecisionSourceUniverse.Closed K)
    (h : InWindow S K (finiteC Γ) q.type q) : ∃ code, slot S K Γ q = some code := by
  obtain ⟨i, _, hi, _⟩ := exact_LeastCodeSpecification S K Γ q.type q hk h
  exact ⟨encodeAddress ⟨Γ, q.type, i⟩, by simp only [slot, hi, Option.map_some]⟩

private theorem mappedCodes {S K Γ xs codes} (h : Slots S K Γ xs codes) :
    xs.toList.map (fun q => (slot S K Γ q).getD 0) = codes := by
  have hMap := congrArg (List.map (fun code : Option Nat => code.getD 0)) h
  simpa [List.map_map, Function.comp_def] using hMap

private theorem typedCodes {S K Γ xs codes}
    (hWindow : ∀ q ∈ xs.toList, InWindow S K (finiteC Γ) q.type q)
    (h : Slots S K Γ xs codes) : TypedAddressList S K codes := by
  intro code hc
  have hm : some code ∈ xs.toList.map (slot S K Γ) :=
    (show xs.toList.map (slot S K Γ) = codes.map some from h).symm ▸
      List.mem_map.mpr ⟨code, hc, rfl⟩
  obtain ⟨q, hq, hCode⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, hAddress⟩ := slotCode hCode
  let Q : WindowCarrier S K (finiteC Γ) q.type := ⟨q, hWindow q hq⟩
  exact ⟨Γ, q.type, i, classOf Q, hAddress, Q, rfl, hi⟩

theorem argument : RawArgumentAddressDescent := by
  intro S K Γ source target sourceCodes targetCodes hk hSource hTarget hStep hSrcCodes hDstCodes
  obtain ⟨front, suffix, before, after, hSrc, hDst, hRaw⟩ := location source target hStep
  have hBefore : InWindow S K (finiteC Γ) before.type before :=
    hSource before (by rw [hSrc]; exact List.mem_append_right _ List.mem_cons_self)
  have hAfter : InWindow S K (finiteC Γ) after.type after :=
    hTarget after (by rw [hDst]; exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨old, hOld⟩ := actualCode hk hBefore
  obtain ⟨new, hNew⟩ := actualCode hk hAfter
  have hPositive := positive S K Γ before after old new hk hBefore hAfter hRaw hOld hNew
  let address := fun q : NTerm => (slot S K Γ q).getD 0
  have hSrcOrder : sourceCodes = front.map address ++ old :: suffix.map address := by
    have hMap := mappedCodes hSrcCodes
    rw [hSrc, List.map_append, List.map_cons] at hMap
    simpa only [address, hOld, Option.getD_some] using hMap.symm
  have hDstOrder : targetCodes = front.map address ++ new :: suffix.map address := by
    have hMap := mappedCodes hDstCodes
    rw [hDst, List.map_append, List.map_cons] at hMap
    simpa only [address, hNew, Option.getD_some] using hMap.symm
  refine ⟨?_, front.map address, suffix.map address, old, new, hSrcOrder, hDstOrder, hPositive⟩
  refine ⟨typedCodes hSource hSrcCodes, typedCodes hTarget hDstCodes,
    front.map address ++ suffix.map address, [old], [new], ?_, ?_, by simp, ?_⟩
  · rw [hSrcOrder]
    exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  · rw [hDstOrder]
    exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  · intro code hCode
    have hEq := List.mem_singleton.mp hCode
    subst code
    exact ⟨old, List.mem_cons_self, hPositive⟩

end LogicLineages.PersistentMarking.NumberedWindowConstructorRawArgumentProof
