import LogicLineages.PersistentMarking.NumberedWindowConfinedRankMapTargets
import LogicLineages.PersistentMarking.DecisionInventoryProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationRealizationProof

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedRankMapProof
open Spine NumberedWindowDomain NumberedWindowOrdinaryTranslation NumberedWindowSimulationData
open NumberedWindowConfinedRankMap NumberedWindowConfinedRankMapTargets
open NumberedWindowFixedConfinedSimulationChecks

theorem initialGuard : InitialConfinedWindowGuard := by
  intro S q τ typed ordinary
  have exactSupport := DecisionInventoryProof.ordinaryExact EmptyContext q τ typed.1 ordinary
  refine ⟨?_, ⟨⟨q, typed, ordinary, fun _ h => h⟩, rfl⟩⟩
  intro a ha b hb
  exact (exactSupport b).mp
    (DecisionInventoryProof.auxiliaryClosed q a ((exactSupport a).mpr ha) b hb)

theorem predecessorGuard : ConfinedPredecessorInGuard := by
  intro S K τ q t guard edge
  obtain ⟨υ, sourceTyped, targetTyped, _, targetOrdinary⟩ := edge.1
  have same : υ = τ := (NumberedWindowSimulationRealizationProof.paperType sourceTyped).symm.trans
    (NumberedWindowSimulationRealizationProof.paperType guard.1)
  subst υ
  exact ⟨targetTyped, targetOrdinary, fun a ha => guard.2.2 a (edge.2.2 a ha)⟩

theorem quoteLiteral : GuardedQuoteLiteral := by
  intro S K τ q Q hQ h
  let witness := exact_OrdinaryQuoteInSuppliedWindow S K q.val τ q.property.1 q.property.2.1 q.property.2.2
  have literal : Classical.choose witness = Q :=
    Option.some.inj ((Classical.choose_spec witness).1.symm.trans h)
  change classOf (⟨Classical.choose witness, (Classical.choose_spec witness).2⟩ :
    WindowCarrier S K EmptyContext τ) = classOf ⟨Q, hQ⟩
  exact congrArg (@classOf S K EmptyContext τ) (Subtype.ext literal)

theorem preservesStrict : GuardedQuotePreservesStrict := by
  intro S K τ hk source target edge
  rcases source with ⟨s, hs⟩
  rcases target with ⟨t, ht⟩
  have same := NumberedWindowSimulationRealizationProof.paperType hs.1
  subst τ
  obtain ⟨Q, T, qs, qt, hQ, hT, path⟩ :=
    exact_PositiveConfinedSimulationInSuppliedWindow S K s t hk hs.2.2 edge
  rw [quoteLiteral S K s.type ⟨s, hs⟩ Q hQ qs, quoteLiteral S K s.type ⟨t, ht⟩ T hT qt]
  exact path

end LogicLineages.PersistentMarking.NumberedWindowConfinedRankMapProof
