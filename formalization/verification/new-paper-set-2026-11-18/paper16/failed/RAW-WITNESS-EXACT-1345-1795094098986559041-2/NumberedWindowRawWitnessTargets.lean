import LogicLineages.PersistentMarking.NumberedWindowRawWitnessBits

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessTargets
open Spine NumberedWindowSyntax NumberedWindowRules
open NumberedWindowRawWitnessRootBits NumberedWindowRawWitnessBits

def ExactPrecedenceBit : Prop :=
  ∀ S f g, precedesBit S f g = true ↔ Precedes S f g

def ExactEquivalentHeadBit : Prop :=
  ∀ S f g, equivalentBit S f g = true ↔ Equivalent S f g

def SuppliedRawWitnessSound : Prop :=
  (∀ S K w Q R, rawBit S K w Q R = true → RawStep S K Q R) ∧
  (∀ S K i w qs rs, argsAtBit (rawBit S K w) i qs rs = true → RawArgsStep S K qs rs)

def ExactCertifiedRawStep : Prop :=
  ∀ S K Q R, (∃ w, rawBit S K w Q R = true) ↔ RawStep S K Q R

def ExactCertifiedRawArgsStep : Prop :=
  ∀ S K qs rs, (∃ i w, argsAtBit (rawBit S K w) i qs rs = true) ↔ RawArgsStep S K qs rs

def ExactCertifiedFiniteWindowStep : Prop :=
  ∀ S K Γ τ Q R, (∃ w, finiteWindowWitnessBit S K Γ τ w Q R = true) ↔
    WindowStep S K (BoundContext.«prefix» Γ EmptyContext) τ Q R

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessTargets
