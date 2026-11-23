module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16UniformEffectiveTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeTowerCodeTargets

@[expose] public section

/-! The conditional principal theorem with a primitive-recursive code for the
actual printed native tower sequence. The code and its calibration occur in
the conclusion, not among the five retained ordinal/accessibility hypotheses. -/

namespace LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveCodedTargets
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets NativeRankTargets
open NativeTowerSequenceTargets ConditionalHeightTargets ConditionalMain16Targets
open ExternalOrdinalInterfaceTargets ConditionalTowerCofinality

universe u

def CodedEffectiveCofinalFamily (BH : Ordinal.{0}) : Prop :=
  Primrec NativeTowerCode.sequenceCode ∧
  ∀ S (wfFull : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t))
    (wfNative : WellFounded (@NativeBelow S indexType)),
    ∃ t : Nat → ClosedNativeTerm S indexType,
      (∀ n, (t n).val = sequenceTerm n) ∧
      (∀ n, NativeSyntaxCountabilityTargets.nativeCode (t n) = NativeTowerCode.sequenceCode n) ∧
      (∀ β, β < BH → ∃ n, β < nativeRank (wfNative.apply (t n))) ∧
      (∀ n, nativeRank (wfNative.apply (t n)) < BH) ∧
      (∀ q τ, PaperTerm S q τ → Ordinary q → confinedRank (wfFull.apply q) ≠ BH)

def Main16StatementCodedEffective (BH : Ordinal.{0}) : Prop :=
  Items1to5 ∧ UpperBound BH ∧ HeightIsBH BH ∧ CodedEffectiveCofinalFamily BH

def ConditionalMain16UniformEffectiveCoded : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}),
    ExternalOrdinalInterfaceID1Targets.NormTheorem BH →
    ConditionalUpperUniformTargets.UniformAccessibility →
    Calibration D → TowerHypotheses D → BHIdentification D BH →
    Main16StatementCodedEffective BH

end LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveCodedTargets
