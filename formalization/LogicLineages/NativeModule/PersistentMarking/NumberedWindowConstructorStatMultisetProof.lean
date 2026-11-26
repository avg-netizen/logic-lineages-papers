module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorStatMarkProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticLeastClassChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorStatMultisetProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextTargets
open NumberedWindowConstructorArgumentAddresses NumberedWindowArithmeticDirectMultisetTargets
open NumberedWindowConstructorStatAddressTargets NumberedWindowConstructorStatMarkProof

private theorem collect {S K Γ} (hk : DecisionSourceUniverse.Closed K) (xs : List NTerm)
    (h : ∀ q ∈ xs, InWindow S K (finiteC Γ) q.type q) :
    ∃ codes : List Nat, xs.map (slot S K Γ) = codes.map some := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons q tail ih =>
    obtain ⟨i, _, hi, _⟩ := exact_LeastCodeSpecification S K Γ q.type q hk (h q List.mem_cons_self)
    obtain ⟨codes, hTail⟩ := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    exact ⟨encodeAddress ⟨Γ, q.type, i⟩ :: codes,
      by simp only [List.map_cons, slot, hi, Option.map_some, hTail]⟩

private theorem originOfCode {S K Γ code} {xs : List NTerm} {codes : List Nat}
    (h : xs.map (slot S K Γ) = codes.map some) (hc : code ∈ codes) :
    ∃ q ∈ xs, slot S K Γ q = some code := by
  have hm : some code ∈ xs.map (slot S K Γ) := h.symm ▸ List.mem_map.mpr ⟨code, hc, rfl⟩
  exact List.mem_map.mp hm

private theorem codeOfOrigin {S K Γ q} {xs : List NTerm} {codes : List Nat}
    (h : xs.map (slot S K Γ) = codes.map some) (hq : q ∈ xs) :
    ∃ code ∈ codes, slot S K Γ q = some code := by
  have hm : slot S K Γ q ∈ codes.map some := h ▸ List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨code, hc, he⟩ := List.mem_map.mp hm
  exact ⟨code, hc, he.symm⟩

private theorem typedCodes {S K Γ} {xs : List NTerm} {codes : List Nat}
    (hWindow : ∀ q ∈ xs, InWindow S K (finiteC Γ) q.type q)
    (h : xs.map (slot S K Γ) = codes.map some) : TypedAddressList S K codes := by
  intro code hc
  obtain ⟨q, hq, hCode⟩ := originOfCode h hc
  obtain ⟨i, hi, hAddress⟩ := slotCode hCode
  let Q : WindowCarrier S K (finiteC Γ) q.type := ⟨q, hWindow q hq⟩
  exact ⟨Γ, q.type, i, classOf Q, hAddress, Q, rfl, hi⟩

private theorem mappedPartition {S K Γ} {xs kept rest : List NTerm}
    {addresses keepAddresses restAddresses : List Nat}
    (h : xs.Perm (kept ++ rest))
    (hSource : xs.map (slot S K Γ) = addresses.map some)
    (hKept : kept.map (slot S K Γ) = keepAddresses.map some)
    (hRest : rest.map (slot S K Γ) = restAddresses.map some) :
    addresses.Perm (keepAddresses ++ restAddresses) := by
  have hp := h.map (slot S K Γ)
  rw [hSource, List.map_append, hKept, hRest, ← List.map_append] at hp
  simpa [List.map_map, Function.comp_def] using hp.map (fun c : Option Nat => c.getD 0)

theorem primitive : PrimitiveReplacementAddressDescent := by
  intro S K Γ source target sourceCodes hk hSource hStep hSourceCodes
  obtain ⟨kept, removed, added, pSource, pTarget, hNonempty, hDominators⟩ := hStep
  have hKept : ∀ q ∈ kept, InWindow S K (finiteC Γ) q.type q :=
    fun q hq => hSource q (pSource.mem_iff.mpr (List.mem_append_left _ hq))
  have hRemoved : ∀ q ∈ removed, InWindow S K (finiteC Γ) q.type q :=
    fun q hq => hSource q (pSource.mem_iff.mpr (List.mem_append_right _ hq))
  have hAdded : ∀ q ∈ added, InWindow S K (finiteC Γ) q.type q := by
    intro q hq
    obtain ⟨origin, ho, hMark⟩ := hDominators q hq
    obtain ⟨hTarget, _⟩ := carrierPath hk (hRemoved origin ho) hMark
    exact NumberedWindowPreservationGuardProof.annotated hTarget
  have hTarget : ∀ q ∈ target.toList, InWindow S K (finiteC Γ) q.type q :=
    fun q hq => (List.mem_append.mp (pTarget.mem_iff.mp hq)).elim (hKept q) (hAdded q)
  obtain ⟨keepAddresses, hKeepAddresses⟩ := collect hk kept hKept
  obtain ⟨removeAddresses, hRemoveAddresses⟩ := collect hk removed hRemoved
  obtain ⟨addAddresses, hAddAddresses⟩ := collect hk added hAdded
  obtain ⟨targetCodes, hTargetCodes⟩ := collect hk target.toList hTarget
  refine ⟨targetCodes, hTargetCodes, typedCodes hSource hSourceCodes, typedCodes hTarget hTargetCodes,
    keepAddresses, removeAddresses, addAddresses,
    mappedPartition pSource hSourceCodes hKeepAddresses hRemoveAddresses,
    mappedPartition pTarget hTargetCodes hKeepAddresses hAddAddresses, ?_, ?_⟩
  · intro hEmpty
    have hMappedEmpty : removed.map (slot S K Γ) = [] := by
      simp only [hRemoveAddresses, hEmpty, List.map_nil]
    exact hNonempty (List.map_eq_nil_iff.mp hMappedEmpty)
  · intro addr ha
    obtain ⟨a, ha', hAddress⟩ := originOfCode hAddAddresses ha
    obtain ⟨origin, ho, hMark⟩ := hDominators a ha'
    obtain ⟨src, hSrc, hOriginCode⟩ := codeOfOrigin hRemoveAddresses ho
    exact ⟨src, hSrc, addresses S K Γ origin a src addr hk (hRemoved origin ho) hMark hOriginCode hAddress⟩

end LogicLineages.PersistentMarking.NumberedWindowConstructorStatMultisetProof
