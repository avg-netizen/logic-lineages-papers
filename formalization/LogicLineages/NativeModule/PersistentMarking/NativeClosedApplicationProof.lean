module

public import LogicLineages.NativeModule.PersistentMarking.NativeClosedApplicationTargets
public import LogicLineages.NativeModule.PersistentMarking.StructuralContextProof
public import LogicLineages.NativeModule.PersistentMarking.TypeSupportConfinementProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeClosedApplicationProof
open Spine StructuralContext
open NativeClosedApplication NativeClosedApplicationTargets

theorem literal : LiteralNativeApplication := by
  intro S σ τ f a
  rfl

theorem functionStrict : NativeApplicationFunctionStrict := by
  intro S σ τ s t a edge
  let C : Context := .head (.app σ τ) .nil .hole (.cons a.val .nil)
  have ha := a.property.1
  have typed : ContextTyped S C (.arrow σ τ) τ :=
    .head .hole ⟨0, rfl⟩ .nil True.intro True.intro
      (.cons ha.1.1 .nil) ⟨ha.1.2, True.intro⟩ ⟨ha.2.1, True.intro⟩ rfl
  have hs := s.property.1
  have ht := t.property.1
  have source := (applyClosed s a).property.1
  have target := (applyClosed t a).property.1
  change ConfinedPair.Strict S (fill C s.val) (fill C t.val)
  refine ⟨⟨τ, source.1, target.1, source.2.1, target.2.1⟩, ?_, ?_⟩
  · exact StructuralContextProof.strictContext S C (.arrow σ τ) τ s.val t.val
      typed hs.1 ht.1 hs.2.1 ht.2.1 edge.2.1
  · exact TypeSupportConfinementProof.contextConfinement S C (.arrow σ τ) τ s.val t.val
      typed hs.1 ht.1 hs.2.1 ht.2.1 edge.2.2

end LogicLineages.PersistentMarking.NativeClosedApplicationProof
