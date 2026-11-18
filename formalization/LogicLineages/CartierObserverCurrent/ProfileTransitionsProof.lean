module
public import LogicLineages.CartierObserverCurrent.ProfileTransitionsTargets
public import LogicLineages.CartierObserverCurrent.ProfileDescentProof
public import LogicLineages.CartierObserverCurrent.LocalPolynomialProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.ProfileTransitions
open SplittingRoots

private noncomputable instance rootFintype (d : Nat) : Fintype (Root d) := by
  classical
  unfold Root
  infer_instance

private theorem cartier_zero (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2] :
    Basic.actualDifferentialCartier (0 : RatFunc K) = 0 := by
  simpa using Basic.actualDifferentialCartierCharacterization K 0 0

private theorem step_add (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    (i : Bool) (f g : RatFunc K) :
    MixedProper.step i (f + g) = MixedProper.step i f + MixedProper.step i g := by
  cases i <;> simp only [MixedProper.step, Bool.false_eq_true, if_false, if_true,
    mul_add, Basic.cartierAdd]

private theorem step_sum (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    (i : Bool) {ι : Type*} (s : Finset ι) (f : ι → RatFunc K) :
    MixedProper.step i (∑ z ∈ s, f z) = ∑ z ∈ s, MixedProper.step i (f z) := by
  classical
  induction s using Finset.induction_on with
  | empty => cases i <;> simp [MixedProper.step, cartier_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, step_add, ih]

private theorem step_pole (d : Nat) (i : Bool) (b : Root d → FieldAt d) (z : Root d) :
    MixedProper.step i (Basic.rationalC (b z) / (Basic.rationalX - Basic.rationalC z.val)) =
      Basic.rationalC (step d i b z) / (Basic.rationalX - Basic.rationalC z.val) := by
  cases i
  · have h := (Basic.evenSelectorLocalPowers (FieldAt d) z.val (b z) (-1)).2
    norm_num only at h
    simpa only [step, MixedProper.step, Bool.false_eq_true, if_false,
      zpow_neg_one, div_eq_mul_inv] using h
  · have h := ((Basic.LocalPolynomial.localPolePolynomialRule (FieldAt d)).1 z.val (b z) 0).2
    simpa only [step, MixedProper.step, if_true, Nat.mul_zero, Nat.zero_add,
      pow_one] using h

theorem actualIntertwining : Targets.ActualIntertwining := by
  intro d i b
  classical
  unfold RationalCoverage.reconstruct
  rw [step_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact step_pole d i b z

theorem compatiblePreservation : Targets.CompatiblePreservation := by
  intro d i b hb
  apply (ProfileDescent.compatibilityFixed d _).mpr
  rw [← actualIntertwining, Naturality.extensionStep,
    (ProfileDescent.compatibilityFixed d b).mp hb]

theorem basePreservation : Targets.BasePreservation := by
  intro d i g hg
  constructor
  · exact MixedProper.stepProper (ZMod 2) i g hg.1
  · change (Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) (MixedProper.step i g)).denom ∣ _
    rw [Naturality.extensionStep]
    exact (MixedProper.stepDenominatorDivides (FieldAt d) i (ProfileDescent.extend d g)).trans hg.2

theorem actualBaseSquare : Targets.ActualBaseSquare := by
  intro d i g b h
  change Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) (MixedProper.step i g) = _
  rw [Naturality.extensionStep]
  change MixedProper.step i (ProfileDescent.extend d g) = _
  rw [h, actualIntertwining]

#audit_namespace LogicLineages.CartierObserverCurrent.ProfileTransitions
end LogicLineages.CartierObserverCurrent.ProfileTransitions
