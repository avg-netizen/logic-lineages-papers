module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationProtectionProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationGrammarProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialProof
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationProof
import LogicLineages.PermittedControl.ArbitraryHeadWireListAssignmentsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees extend extendAgrees)
open OriginalPrintedCircuitSequential (Graphs exactPrintedCircuitRun)

theorem exactPrintedNormalizedExtension : ExactPrintedNormalizedExtension := by
  intro f ext gates ν
  let n := firstHidden ext gates
  let aliases := entries ext gates
  let norm := normalized ext gates
  obtain ⟨_,bounds,beyond⟩ := exactPrintedProtection ext gates
  have keep (θ : Valuation) (agree : Agrees aliases ν θ) (p : Nat)
      (bound : p ≤ protectedCeiling ext gates) : θ p = ν p :=
    agree p (fun mem => (Nat.not_lt_of_ge bound) (beyond p mem))
  have field (θ : Valuation) (agree : Agrees aliases ν θ) :=
    fieldsStable f ν θ gates (fun g hg =>
      ⟨keep θ agree _ (bounds g hg).1, fun p hp => keep θ agree _ ((bounds g hg).2 p hp)⟩)
  have reduced := (OriginalMixedGateNormalization.exactMixedNormalizedExtension
    f (protectedCeiling ext gates) (baseGates gates) ν).1
  have equiv (θ : Valuation) : (Holds f θ norm ∧ Agrees aliases ν θ) ↔
      Graphs f ν gates ∧ θ = extend ν aliases := by
    constructor
    · rintro ⟨all,agree⟩
      obtain ⟨base,flds⟩ := (normalizedSplit f θ gates n).mp all
      obtain ⟨original,shape⟩ := (reduced θ).mp ⟨base,agree⟩
      exact ⟨(originalSplit f ν gates).mpr ⟨original,(field θ agree).mp flds⟩,shape⟩
    · rintro ⟨original,rfl⟩
      obtain ⟨base,flds⟩ := (originalSplit f ν gates).mp original
      have checked := (reduced (extend ν aliases)).mpr ⟨base,rfl⟩
      exact ⟨(normalizedSplit f (extend ν aliases) gates n).mpr
        ⟨checked.1,(field _ checked.2).mpr flds⟩,checked.2⟩
  refine ⟨equiv,?_,?_⟩
  · constructor
    · rintro ⟨θ,h,_⟩
      exact ((equiv θ).mp h).1
    · intro orig
      exact ⟨extend ν aliases,(equiv _).mpr ⟨orig,rfl⟩,fun other h => ((equiv other).mp h).2⟩
  · intro p bound
    exact keep _ (extendAgrees aliases ν) p bound

theorem exactPrintedRunThenNormalize : ExactPrintedRunThenNormalize := by
  intro f known gates top ext base final
  have seq := exactPrintedCircuitRun f known gates top base final
  have hidden := (exactPrintedNormalizedExtension f ext gates final).2.1
  exact seq.trans ⟨fun h => ⟨h.2,hidden.mpr h.1⟩,fun h => ⟨hidden.mp h.2,h.1⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
