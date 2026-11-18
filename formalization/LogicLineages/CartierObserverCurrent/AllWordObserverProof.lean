module
public import LogicLineages.CartierObserverCurrent.AllWordObserverTargets
public import LogicLineages.CartierObserverCurrent.RegularSelectorsProof
public import LogicLineages.CartierObserverCurrent.ProfileTransitionsProof
public import LogicLineages.CartierObserverCurrent.ProfileOutputProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.AllWordObserver
open SplittingRoots

theorem wordRegular : Targets.WordRegular := by
  intro f hf w
  induction w generalizing f with
  | nil => exact hf
  | cons i w ih => exact ih (MixedProper.step i f) (RegularSelectors.regularPreservation f hf i)

theorem wordCoefficient : Targets.WordCoefficient := by
  intro f hf w
  induction w generalizing f with
  | nil => intro n; simp [MixedWord.execute, offset]
  | cons i w ih =>
    intro n
    rw [MixedWord.execute, ih _ (RegularSelectors.regularPreservation f hf i),
      RegularSelectors.actualCoefficientSelector f hf i]
    congr 1
    cases i <;> simp [offset, Nat.bit, pow_succ] <;> ring

theorem offsetAppend : Targets.OffsetAppend := by
  intro p w
  induction p with
  | nil => simp [offset]
  | cons i p ih =>
    cases i <;> simp [offset, Nat.bit, ih, pow_succ] <;> ring

theorem profileExecution : Targets.ProfileExecution := by
  intro d w
  induction w with
  | nil => intro b; rfl
  | cons i w ih =>
    intro b
    rw [execute, ih, ← ProfileTransitions.actualIntertwining]
    rfl

theorem compatibleExecution : Targets.CompatibleExecution := by
  intro d b hb w
  induction w generalizing b with
  | nil => exact hb
  | cons i w ih => exact ih _ (ProfileTransitions.compatiblePreservation d i b hb)

theorem baseObservation : Targets.BaseObservation := by
  intro d g b hg w
  have hreg : RegularSelectors.regular g := (ProfileOutput.actualBaseOutput d g b hg).1
  have hword : ProfileDescent.extend d (MixedWord.execute w g) =
      RationalCoverage.reconstruct d (execute d w b) := by
    unfold ProfileDescent.extend
    rw [Naturality.extensionWord, profileExecution]
    change MixedWord.execute w (ProfileDescent.extend d g) = _
    rw [hg]
  have ho := (ProfileOutput.actualBaseOutput d (MixedWord.execute w g) (execute d w b) hword).2
  change algebraMap (ZMod 2) (FieldAt d)
    ((RegularSelectors.expansion (MixedWord.execute w g)).coeff 0) = _ at ho
  rw [wordCoefficient g hreg w 0, Nat.mul_zero, Nat.zero_add] at ho
  exact ho.symm

#audit_namespace LogicLineages.CartierObserverCurrent.AllWordObserver
end LogicLineages.CartierObserverCurrent.AllWordObserver
