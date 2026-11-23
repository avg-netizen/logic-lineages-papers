module

public import LogicLineages.NativeModule.PersistentMarking.StablePairTargets
public import LogicLineages.NativeModule.PersistentMarking.TypeSupportConfinementProof
public import LogicLineages.NativeModule.PersistentMarking.StructuralStabilityProof
public import LogicLineages.NativeModule.PersistentMarking.OrdinaryCompositionProof
public import LogicLineages.NativeModule.PersistentMarking.FreeVariableProof

@[expose] public section

namespace LogicLineages.PersistentMarking.StablePairProof
open Spine TypeSupport

theorem ordinaryEndpoints {S : Signature} {s t : Expr} (h : ConfinedPair.Domain S s t) : Ordinary s ∧ Ordinary t := by
  obtain ⟨τ,hs,ht,hos,hot⟩ := h
  exact ⟨hos,hot⟩

theorem domainTrans {S : Signature} {s t u : Expr}
    (h : ConfinedPair.Domain S s t) (k : ConfinedPair.Domain S t u) : ConfinedPair.Domain S s u := by
  obtain ⟨τ,hs,ht,hos,hot⟩ := h
  obtain ⟨υ,ht',hu,hot',hou⟩ := k
  have he : τ = υ := (SpineShiftProof.annotationExact _ _ _ ht.1).symm.trans
    (SpineShiftProof.annotationExact _ _ _ ht'.1)
  subst υ
  exact ⟨τ,hs,hu,hos,hou⟩

theorem includedTrans {s t u : Expr} (h : Included t s) (k : Included u t) : Included u s :=
  fun ρ hr => h ρ (k ρ hr)

theorem weakReflexive : StablePairTargets.WeakReflexive := by
  intro S q τ hp ho
  exact ⟨⟨τ,hp,hp,ho,ho⟩,ElementaryProof.ordinaryReflexive S q τ hp ho,fun _ h => h⟩

theorem weakTransitive : StablePairTargets.WeakTransitive := by
  intro S s t u h k
  exact ⟨domainTrans h.1 k.1,
    OrdinaryCompositionProof.weakWeak S s t u (ordinaryEndpoints h.1).1 (ordinaryEndpoints h.1).2
      (ordinaryEndpoints k.1).2 h.2.1 k.2.1,includedTrans h.2.2 k.2.2⟩

theorem strictIncluded : StablePairTargets.StrictIncluded := by
  intro S s t h
  exact ⟨h.1,ElementaryProof.strictIncluded S s t h.2.1,h.2.2⟩

theorem strictTransitive : StablePairTargets.StrictTransitive := by
  intro S s t u h k
  exact ⟨domainTrans h.1 k.1,
    OrdinaryCompositionProof.strictStrict S s t u (ordinaryEndpoints h.1).1 (ordinaryEndpoints h.1).2
      (ordinaryEndpoints k.1).2 h.2.1 k.2.1,includedTrans h.2.2 k.2.2⟩

theorem weakStrict : StablePairTargets.WeakStrict := by
  intro S s t u h k
  exact ⟨domainTrans h.1 k.1,
    OrdinaryCompositionProof.weakStrict S s t u (ordinaryEndpoints h.1).1 (ordinaryEndpoints h.1).2
      (ordinaryEndpoints k.1).2 h.2.1 k.2.1,includedTrans h.2.2 k.2.2⟩

theorem strictWeak : StablePairTargets.StrictWeak := by
  intro S s t u h k
  exact ⟨domainTrans h.1 k.1,
    OrdinaryCompositionProof.strictWeak S s t u (ordinaryEndpoints h.1).1 (ordinaryEndpoints h.1).2
      (ordinaryEndpoints k.1).2 h.2.1 k.2.1,includedTrans h.2.2 k.2.2⟩

theorem subDomain {S : Signature} {s t : Expr} {θ : FreeMap}
    (h : ConfinedPair.Domain S s t) (hm : StructuralStabilityTargets.OrdinaryMap S θ) :
    ConfinedPair.Domain S (freeSub θ 0 s) (freeSub θ 0 t) := by
  obtain ⟨τ,hs,ht,hos,hot⟩ := h
  have htyped : FreeMapTyped EmptyContext θ := fun σ x => (hm σ x).1.1
  have hvalid := fun σ x => (hm σ x).1.2
  exact ⟨τ,RefinementSubstitutionSupport.subPaper S θ htyped hvalid s τ hs,
    RefinementSubstitutionSupport.subPaper S θ htyped hvalid t τ ht,
    StructuralSubstitutionProof.ordinary θ (fun σ x => (hm σ x).2) 0 s hos,
    StructuralSubstitutionProof.ordinary θ (fun σ x => (hm σ x).2) 0 t hot⟩

theorem weakSubstitution : StablePairTargets.WeakSubstitution := by
  intro S s t θ h hm
  obtain ⟨τ,hs,ht,hos,hot⟩ := h.1
  exact ⟨subDomain h.1 hm,StructuralSubstitutionProof.weakSubstitution S s t θ hos hot hm h.2.1,
    TypeSupportConfinementProof.substitutionConfinement S s t τ θ hs ht hos hot h.2.2
      (FreeVariableProof.weakContainment S s t h.2.1) hm⟩

theorem strictSubstitution : StablePairTargets.StrictSubstitution := by
  intro S s t θ h hm
  obtain ⟨τ,hs,ht,hos,hot⟩ := h.1
  exact ⟨subDomain h.1 hm,StructuralSubstitutionProof.strictSubstitution S s t θ hos hot hm h.2.1,
    TypeSupportConfinementProof.substitutionConfinement S s t τ θ hs ht hos hot h.2.2
      (FreeVariableProof.strictContainment S s t h.2.1) hm⟩

theorem contextDomain {S : Signature} {C : StructuralContext.Context} {σ τ : Ty} {s t : Expr}
    (hc : StructuralContext.ContextTyped S C σ τ) (hs : PaperTerm S s σ) (ht : PaperTerm S t σ)
    (h : ConfinedPair.Domain S s t) : ConfinedPair.Domain S (StructuralContext.fill C s) (StructuralContext.fill C t) :=
  ⟨τ,StructuralFillProof.fillPaper S C σ τ s hc hs,StructuralFillProof.fillPaper S C σ τ t hc ht,
    StructuralFillProof.fillOrdinary S C σ τ s hc (ordinaryEndpoints h).1,
    StructuralFillProof.fillOrdinary S C σ τ t hc (ordinaryEndpoints h).2⟩

theorem weakContext : StablePairTargets.WeakContext := by
  intro S C σ τ s t hc hs ht h
  have ho := ordinaryEndpoints h.1
  exact ⟨contextDomain hc hs ht h.1,StructuralContextProof.weakContext S C σ τ s t hc hs ht ho.1 ho.2 h.2.1,
    TypeSupportConfinementProof.contextConfinement S C σ τ s t hc hs ht ho.1 ho.2 h.2.2⟩

theorem strictContext : StablePairTargets.StrictContext := by
  intro S C σ τ s t hc hs ht h
  have ho := ordinaryEndpoints h.1
  exact ⟨contextDomain hc hs ht h.1,StructuralContextProof.strictContext S C σ τ s t hc hs ht ho.1 ho.2 h.2.1,
    TypeSupportConfinementProof.contextConfinement S C σ τ s t hc hs ht ho.1 ho.2 h.2.2⟩

theorem fullStablePair : StablePairTargets.FullStablePair :=
  ⟨weakReflexive,weakTransitive,strictIncluded,strictTransitive,weakStrict,strictWeak,
    weakSubstitution,strictSubstitution,weakContext,strictContext⟩
end LogicLineages.PersistentMarking.StablePairProof
