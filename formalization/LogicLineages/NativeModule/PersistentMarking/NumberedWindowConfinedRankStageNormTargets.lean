module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankDominanceTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowAddressClassRankTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOrdinaryTranslation

/-! New target (Opus B, round 3; not a twin). One statement for the compiled part of
`thm:upper`: the confined-strict rank of a typed ordinary term is bounded by the least
stage of the tagged (equivalently the scalar) accessibility operator at the canonical
address of the class of its literal translation `tr q`, in the window `TypeSupport.support q`,
empty bound context (Γ = []), fixed type τ.  The norm side is the class/address side
on which #1455 holds; no fixed-type-versus-whole-universe rank equality is used. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedRankStageNormTargets
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowOrdinaryTranslation NumberedWindowConfinedRankDominanceTargets
open NumberedWindowCanonicalAddressMap NumberedWindowGuardedNormTargets NumberedWindowExternalIDOperators

def ConfinedRankBelowTaggedStageNorm : Prop :=
  ∀ S q τ, PaperTerm S q τ → Ordinary q →
    ∃ hk : DecisionSourceUniverse.Closed (TypeSupport.support q),
    ∃ (Q : NTerm) (hQ : InWindow S (TypeSupport.support q) EmptyContext τ Q),
    ∃ norm : Ordinal.{0},
      tr q = some Q ∧
      IsLeast {a : Ordinal.{0} | ordinalStage (taggedStep S (TypeSupport.support q)) a
        (tagScalar (classAddress (Γ := []) hk (classOf ⟨Q, hQ⟩)))} norm ∧
      IsLeast {a : Ordinal.{0} | ordinalStage (scalarStep S (TypeSupport.support q)) a
        (classAddress (Γ := []) hk (classOf ⟨Q, hQ⟩))} norm ∧
      Acc (OriginalBelow S) q ∧
      ∀ symbolic : Acc (OriginalBelow S) q, symbolic.rank ≤ norm

end LogicLineages.PersistentMarking.NumberedWindowConfinedRankStageNormTargets
