module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableListProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableMultisetProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution
open NumberedBottomVariable NumberedBottomVariableProof NumberedBottomVariableListProof

theorem insertedListInverse {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (ht : BottomOrVariable theta)
    (removed : List (Packed Symbol arity Gamma)) (inserted : List (Packed Symbol arity Delta))
    (h : ∀ q ∈ inserted, ∃ s ∈ removed,
      PrimitiveMark Symbol arity Delta (substitutePacked theta s) q) :
    ∃ lifted : List (Packed Symbol arity Gamma),
      lifted.map (substitutePacked theta) = inserted ∧
      ∀ q ∈ lifted, ∃ s ∈ removed, PrimitiveMark Symbol arity Gamma s q := by
  induction inserted with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons q rest ih =>
    obtain ⟨s,hs,hm⟩ := h q (by simp)
    obtain ⟨q',hq',he⟩ := actualPrimitiveMarkInverse Symbol arity Gamma Delta theta ht s q hm
    obtain ⟨rest',hr,hw⟩ := ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    refine ⟨q' :: rest',?_,?_⟩
    · simp only [List.map_cons,he,hr]
    · intro r hr
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact ⟨s,hs,hq'⟩
      · exact hw r hr

theorem actualPrimitiveMultisetInverse : NumberedBottomVariableTargets.ActualPrimitiveMultisetInverse := by
  intro Symbol arity Gamma Delta theta ht source target hm
  obtain ⟨kept,removed,inserted,hs,htarget,hn,hw⟩ := hm
  obtain ⟨sorted,hsource,hsorted⟩ := mapPermutationInverse (substitutePacked theta) source (kept ++ removed) hs
  obtain ⟨kept',removed',hsplit,hkept,hremoved⟩ :=
    mapAppendSplit (substitutePacked theta) sorted kept removed hsorted
  have hi : ∀ q ∈ inserted, ∃ s ∈ removed',
      PrimitiveMark Symbol arity Delta (substitutePacked theta s) q := by
    intro q hq
    obtain ⟨s,hs,hm⟩ := hw q hq
    rw [← hremoved] at hs
    obtain ⟨s',hs',he⟩ := List.mem_map.mp hs
    exact ⟨s',hs',he.symm ▸ hm⟩
  obtain ⟨inserted',hinserted,hw'⟩ := insertedListInverse theta ht removed' inserted hi
  have htargetMap : ((kept' ++ inserted').map (substitutePacked theta)).Perm target := by
    rw [List.map_append,hkept,hinserted]
    exact htarget.symm
  obtain ⟨target',hperm,he⟩ := mapPermutationInverse (substitutePacked theta)
    (kept' ++ inserted') target htargetMap
  refine ⟨target',⟨kept',removed',inserted',?_,hperm.symm,?_,hw'⟩,he⟩
  · exact hsplit ▸ hsource
  · intro hr
    apply hn
    rw [← hremoved,hr,List.map_nil]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableMultisetProof
