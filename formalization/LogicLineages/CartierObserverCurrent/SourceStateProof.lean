module
public import LogicLineages.CartierObserverCurrent.SourceStateTargets
public import LogicLineages.CartierObserverCurrent.CanonicalExtensionProof
public import LogicLineages.CartierObserverCurrent.SplitSupportProof
public import LogicLineages.CartierObserverCurrent.FullTransientProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.SourceState
open SplittingRoots

theorem wordDenominator : Targets.WordDenominator.{u} := by
  intro K _ _ _ w
  induction w with
  | nil => intro f; exact dvd_refl _
  | cons b w ih =>
    intro f
    exact (ih (MixedProper.step b f)).trans (MixedProper.stepDenominatorDivides K b f)

theorem sourceDenominator : Targets.SourceDenominator := by
  intro d P w
  let f : RatFunc (ZMod 2) := algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) P /
    algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) (SourceBudget.denominator (ZMod 2) d)
  have h : (MixedWord.execute w f).denom ∣ SourceBudget.denominator (ZMod 2) d :=
    (wordDenominator (ZMod 2) w f).trans (RatFunc.denom_div_dvd _ _)
  change (Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) (MixedWord.execute w f)).denom ∣ _
  rw [CanonicalExtension.denominatorMap]
  exact map_dvd (Polynomial.mapRingHom (algebraMap (ZMod 2) (FieldAt d))) h

theorem transientState : Targets.TransientState := by
  intro d hd P hP w hw
  have h := FullTransient.binaryTransient.2.2.2 (ZMod 2) (FieldAt d)
    (algebraMap (ZMod 2) (FieldAt d)) d hd P hP w
  refine ⟨h.1, ?_⟩
  apply SplitSupport.sourceSimpleDivisor d _ (run d P w).denom_ne_zero
    (sourceDenominator d P w)
  exact h.2.2 hw

#audit_namespace LogicLineages.CartierObserverCurrent.SourceState
end LogicLineages.CartierObserverCurrent.SourceState
