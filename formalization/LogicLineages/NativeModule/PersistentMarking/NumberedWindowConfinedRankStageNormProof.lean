module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankStageNormTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankDominanceProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowAddressClassRankProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankMapChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFixedConfinedSimulationChecks

/-! New proof (Opus B, round 3; not a twin) of the frozen
`NumberedWindowConfinedRankStageNormTargets.ConfinedRankBelowTaggedStageNorm`
(sha256 fbc8dfa6…730b).  Pure assembly of #1448 (`exact_OriginalInitialQuoteRankDominance`,
`exact_InitialConfinedWindowGuard`, `exact_GuardedQuoteLiteral`,
`exact_OrdinaryQuoteInSuppliedWindow`) and #1455 (`exact_ActualClassStageNormAtAddress`) at
Γ = [], where `finiteC []` reduces to `EmptyContext`.  Ranks of accessibility proofs agree by
proof irrelevance. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedRankStageNormProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowOrdinaryTranslation NumberedWindowConfinedRankMap NumberedWindowConfinedRankDominanceTargets
open NumberedWindowCanonicalAddressMap NumberedWindowGuardedNormTargets NumberedWindowExternalIDOperators
open NumberedWindowConfinedRankStageNormTargets

private theorem rankCongr {α : Type} {r : α → α → Prop} {x y : α} (e : x = y)
    (a : Acc r x) (b : Acc r y) : a.rank = b.rank := by
  subst e
  rfl

theorem exact_ConfinedRankBelowTaggedStageNorm : ConfinedRankBelowTaggedStageNorm := by
  intro S q τ typed ordinary
  obtain ⟨hk, _, _⟩ :=
    NumberedWindowConfinedRankMapChecks.exact_InitialConfinedWindowGuard S q τ typed ordinary
  obtain ⟨start, symbolicWF, numericalWF, literal, bound⟩ :=
    NumberedWindowConfinedRankDominanceProof.exact_OriginalInitialQuoteRankDominance S q τ typed ordinary
  obtain ⟨Q, translation, hQ⟩ :=
    NumberedWindowFixedConfinedSimulationChecks.exact_OrdinaryQuoteInSuppliedWindow S
      (TypeSupport.support q) q τ typed ordinary (fun _ h => h)
  have startTranslation : tr start.val = some Q := by
    rw [literal]
    exact translation
  have quoted : quote start = classOf ⟨Q, hQ⟩ :=
    NumberedWindowConfinedRankMapChecks.exact_GuardedQuoteLiteral S (TypeSupport.support q) τ start Q hQ
      startTranslation
  obtain ⟨classAcc, scalarLeast, taggedLeast⟩ :=
    NumberedWindowAddressClassRankProof.exact_ActualClassStageNormAtAddress S (TypeSupport.support q) [] τ hk
      (classOf ⟨Q, hQ⟩)
  have numericalRank : (numericalWF.apply (quote start)).rank = classAcc.rank :=
    rankCongr (r := FixedPositiveBelow S (TypeSupport.support q) τ) quoted _ classAcc
  refine ⟨hk, Q, hQ, classAcc.rank, translation, taggedLeast, scalarLeast, symbolicWF.apply q, ?_⟩
  intro symbolic
  have symbolicRank : symbolic.rank = (symbolicWF.apply q).rank := rfl
  rw [symbolicRank, ← numericalRank]
  exact bound

#print axioms exact_ConfinedRankBelowTaggedStageNorm

end LogicLineages.PersistentMarking.NumberedWindowConfinedRankStageNormProof
