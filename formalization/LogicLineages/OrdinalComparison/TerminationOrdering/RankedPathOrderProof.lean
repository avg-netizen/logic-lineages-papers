module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEmbeddingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison RankedTree RankedPathOrder

theorem originalRankedRestriction : RankedPathOrderTargets.OriginalRankedRestriction := by
  intro Symbol arity Gamma above s t
  constructor
  · constructor
    · intro h
      have H := (RankedReflectionProof.weakReflection above h).1 s t rfl rfl
      cases H with
      | equal s t he => exact Or.inl he
      | greater s t hg => exact Or.inr hg
    · intro h
      rcases h with he | hg
      · exact RankedPathEqualityProof.equality above he
      · exact RecursiveComparisonProof.strictWeakInclusion Symbol arity above Gamma _ _
          (RankedPathEmbeddingProof.strict above hg)
  · exact ⟨fun h => RankedReflectionProof.strictReflection above h s t rfl rfl,
      fun h => RankedPathEmbeddingProof.strict above h⟩

theorem groundSupport {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (s : Tree Symbol arity Gamma) : typeSupport (ordinary s)={Ty.ground} := by
  induction s with
  | var v => simp [ordinary,typeSupport,Ty.subtypes]
  | node f args ih =>
    change ({Ty.ground} ∪ Finset.univ.biUnion (fun i => typeSupport (ordinary (args i))))={Ty.ground}
    apply Finset.ext
    intro tau
    constructor
    · intro h
      rcases Finset.mem_union.mp h with hroot | hchild
      · exact hroot
      · obtain ⟨i,hi,harg⟩ := Finset.mem_biUnion.mp hchild
        rw [ih i] at harg
        exact harg
    · intro h
      exact Finset.mem_union_left _ h

theorem confinedRankedRestriction : RankedPathOrderTargets.ConfinedRankedRestriction := by
  intro Symbol arity Gamma above s t
  have hs : typeSupport (ordinary t) ⊆ typeSupport (ordinary s) := by rw [groundSupport t,groundSupport s]
  have hw := originalRankedRestriction Symbol arity Gamma above s t
  have heS := RankedTreeProof.literalEmbedding Symbol arity Gamma s
  have heT := RankedTreeProof.literalEmbedding Symbol arity Gamma t
  constructor
  · change ((RecursiveComparison.Weak Symbol arity above Gamma
      ⟨Ty.ground,embed (ordinary s)⟩ ⟨Ty.ground,embed (ordinary t)⟩) ∧ _) ↔ _
    rw [← heS,← heT]
    exact ⟨fun h => hw.1.mp h.1,fun h => ⟨hw.1.mpr h,hs⟩⟩
  · change ((Strict Symbol arity above Gamma
      ⟨Ty.ground,embed (ordinary s)⟩ ⟨Ty.ground,embed (ordinary t)⟩) ∧ _) ↔ _
    rw [← heS,← heT]
    exact ⟨fun h => hw.2.mp h.1,fun h => ⟨hw.2.mpr h,hs⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderProof
