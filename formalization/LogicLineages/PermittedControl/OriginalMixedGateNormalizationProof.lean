module
public import LogicLineages.PermittedControl.OriginalMixedGateNormalizationTargets
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationFreshProof
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationGrammarProof
import LogicLineages.PermittedControl.OriginalMixedGateSequentialProof
import LogicLineages.PermittedControl.ArbitraryHeadWireListAssignmentsProof
import LogicLineages.PermittedControl.ArbitraryHeadWireListProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedGateNormalization
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees extend extendAgrees exactSharedWireList)
open OriginalMixedGateSequential (exactMixedSequential)

theorem exactMixedNormalizedExtension : ExactMixedNormalizedExtension := by
  intro f ceiling gates ν
  let n := firstHidden ceiling gates
  let entries := collapseEntries ceiling gates
  let norm := normalized ceiling gates
  obtain ⟨_,bounds,fresh,above⟩ := exactMixedFreshAliases ceiling gates
  have keep (θ : Valuation) (agree : Agrees entries ν θ) (p : Nat)
      (bound : p ≤ protectedCeiling ceiling gates) : θ p = ν p :=
    agree p (fun mem => (Nat.not_lt_of_ge bound) (above _ mem))
  have aff (θ : Valuation) (agree : Agrees entries ν θ) :=
    affinesCongruent f ν θ gates (fun g hg =>
      ⟨keep θ agree _ (bounds g hg).1, fun p hp => keep θ agree _ ((bounds g hg).2 p hp)⟩)
  have equiv (θ : Valuation) :
      (Holds f θ norm ∧ Agrees entries ν θ) ↔
        OriginalMixedGateSequential.Graphs f ν gates ∧ θ = extend ν entries := by
    constructor
    · rintro ⟨all,agree⟩
      obtain ⟨affine,collapse⟩ := (normalizedSplit f θ gates n).mp all
      obtain ⟨original,shape⟩ := (exactSharedWireList f entries fresh ν θ).mp ⟨collapse,agree⟩
      exact ⟨(originalAttached f ν gates n).mpr ⟨(aff θ agree).mp affine,original⟩,shape⟩
    · rintro ⟨original,rfl⟩
      obtain ⟨affine,collapse⟩ := (originalAttached f ν gates n).mp original
      have checked := (exactSharedWireList f entries fresh ν (extend ν entries)).mpr ⟨collapse,rfl⟩
      exact ⟨(normalizedSplit f (extend ν entries) gates n).mpr
        ⟨(aff _ checked.2).mpr affine,checked.1⟩,checked.2⟩
  refine ⟨equiv,?_,?_⟩
  · constructor
    · rintro ⟨θ,h,_⟩
      exact ((equiv θ).mp h).1
    · intro original
      exact ⟨extend ν entries,(equiv _).mpr ⟨original,rfl⟩,fun other h => ((equiv other).mp h).2⟩
  · intro p bounded
    exact keep _ (extendAgrees entries ν) p bounded

theorem exactMixedRunThenNormalize : ExactMixedRunThenNormalize := by
  intro f known gates top ceiling base final
  have seq := exactMixedSequential f known gates top base final
  have hidden := (exactMixedNormalizedExtension f ceiling gates final).2.1
  exact seq.trans ⟨fun h => ⟨h.2,hidden.mpr h.1⟩,fun h => ⟨hidden.mp h.2,h.1⟩⟩

end LogicLineages.PermittedControl.OriginalMixedGateNormalization
