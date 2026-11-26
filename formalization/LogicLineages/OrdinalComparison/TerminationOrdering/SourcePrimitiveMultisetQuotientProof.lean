module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorSuppliersTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowOccurrenceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourcePrimitiveMultisetQuotientProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedQuotientPaths

theorem primitiveMarkQuotient {n : Nat} {arity : Fin n → Nat}
    {symbols : List (Fin n)} {S : List Ty} {above : Fin n → Fin n → Prop}
    {Gamma : List Ty} {q r : Packed (Fin n) arity Gamma}
    (hq : InUniverse symbols S q.2) (h : PrimitiveMark (Fin n) arity Gamma q r) :
    PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S q) (representativeCode symbols S r) := by
  cases h with
  | mk k q r hm =>
    exact .step ⟨_,q,r,hq,
      NumberedWindowOccurrenceProof.finiteMarkStep (Fin n) arity symbols S above k Gamma _ q r hm,
      rfl,rfl⟩

theorem actualPrimitiveMultisetQuotientDescent :
    SourceRankedConstructorSuppliersTargets.ActualPrimitiveMultisetQuotientDescent := by
  intro n arity symbols S above Gamma source target hsource h
  obtain ⟨kept,removed,inserted,hs,ht,hn,hi⟩ := h
  refine ⟨kept.map (representativeCode symbols S),removed.map (representativeCode symbols S),
    inserted.map (representativeCode symbols S),?_,?_,?_,?_⟩
  · simpa only [List.map_append] using hs.map (representativeCode symbols S)
  · simpa only [List.map_append] using ht.map (representativeCode symbols S)
  · intro he
    exact hn (List.map_eq_nil_iff.mp he)
  · intro y hy
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
    obtain ⟨r,hr,hm⟩ := hi q hq
    refine ⟨representativeCode symbols S r,List.mem_map.mpr ⟨r,hr,rfl⟩,?_⟩
    exact primitiveMarkQuotient
      (hsource r (hs.mem_iff.mpr (List.mem_append_right kept hr))) hm
end LogicLineages.OrdinalComparison.TerminationOrdering.SourcePrimitiveMultisetQuotientProof
