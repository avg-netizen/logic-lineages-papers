import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetSound

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetDomain
open NumberedWindowArithmeticAllContextTargets NumberedWindowArithmeticAllContextChecks
open NumberedWindowArithmeticDirectMultisetTargets

theorem preserved : StrictReplacementPreservesTypedAddresses := by
  intro S K source target hs h a ha
  obtain ⟨kept,removed,added,hSrc,hDst,_,hDom⟩ := h
  rcases List.mem_append.mp (hDst.mem_iff.mp ha) with hKept | hAdded
  · exact hs a (hSrc.mem_iff.mpr (List.mem_append.mpr (Or.inl hKept)))
  · obtain ⟨b,_,hPath⟩ := hDom a hAdded
    exact (exact_AddressPathDomain S K b a hPath).2

private theorem transport {S K} {source source' target target' : List Nat}
    (ps : source.Perm source') (pt : target.Perm target')
    (h : AddressDirect S K source target) : AddressDirect S K source' target' := by
  obtain ⟨hs,ht,kept,removed,added,hSrc,hDst,hne,hDom⟩ := h
  refine ⟨?_,?_,kept,removed,added,ps.symm.trans hSrc,pt.symm.trans hDst,hne,hDom⟩
  · intro a ha
    exact hs a (ps.mem_iff.mpr ha)
  · intro a ha
    exact ht a (pt.mem_iff.mpr ha)

theorem permutations : DirectMultisetRespectsPermutations := by
  intro S K source source' target target' ps pt
  exact ⟨transport ps pt,transport ps.symm pt.symm⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetDomain
