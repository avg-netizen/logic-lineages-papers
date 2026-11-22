module
public import LogicLineages.PermittedControl.ActualSignedReadMassTargets
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedReadMass
open PreparedProjection ActualZeroClassReplacement ActualWeightedReadNormalization

private def groupedMass (weights : LowerOperand →₀ Int) : Nat :=
  ∑ op ∈ weights.support, (weights op).natAbs

private theorem expandMass (weights : LowerOperand →₀ Int) (carrier : Finset LowerOperand)
    (encloses : weights.support ⊆ carrier) :
    groupedMass weights = ∑ op ∈ carrier, (weights op).natAbs := by
  unfold groupedMass
  apply Finset.sum_subset encloses
  intro op _ absent
  rw [Finsupp.notMem_support_iff.mp absent,Int.natAbs_zero]

private theorem massAdd (a b : LowerOperand →₀ Int) :
    groupedMass (a+b) ≤ groupedMass a + groupedMass b := by
  classical
  let carrier := a.support ∪ b.support
  rw [expandMass (a+b) carrier Finsupp.support_add,
    expandMass a carrier Finset.subset_union_left,expandMass b carrier Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun op _ => Int.natAbs_add_le (a op) (b op)

private theorem massSingle (op : LowerOperand) (w : Int) :
    groupedMass (Finsupp.single op w) = w.natAbs := by
  classical
  rw [expandMass (Finsupp.single op w) {op} Finsupp.support_single_subset,
    Finset.sum_singleton,Finsupp.single_eq_same]

private theorem groupedBound (raw : List Read) : groupedMass (groupedWeights raw) ≤ signedMass raw := by
  induction raw with
  | nil => simp [groupedMass,groupedWeights,signedMass]
  | cons rd raw ih =>
      change groupedMass (Finsupp.single rd.1.2 rd.1.1 + groupedWeights raw) ≤
        rd.1.1.natAbs + signedMass raw
      exact (massAdd _ _).trans (Nat.add_le_add ((massSingle _ _).le) ih)

theorem exactNormalizedMass : ExactNormalizedMass := by
  classical
  intro f ρ raw xs normalized
  have paid : liftedReads f ρ raw := by
    by_contra unpaid
    have failure := (exactNormalizedReads f ρ raw).1.mpr unpaid
    rw [normalized] at failure
    cases failure
  obtain ⟨out,success,keys,_,_,_,records⟩ := (exactNormalizedReads f ρ raw).2 paid
  have identical : out = xs := Option.some.inj (success.symm.trans normalized)
  subst out
  have occurrenceWeights : xs.map (fun rd => rd.1.1.natAbs) =
      (xs.map (fun rd => rd.1.2)).map (fun op => (groupedWeights raw op).natAbs) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro rd member
    exact congrArg Int.natAbs (records rd member).1
  have calibration : signedMass xs = groupedMass (groupedWeights raw) := by
    unfold signedMass groupedMass
    rw [occurrenceWeights,keys,Finset.sum_map_toList]
  exact calibration.le.trans (groupedBound raw)

end LogicLineages.PermittedControl.ActualSignedReadMass
