import LogicLineages.PersistentMarking.NumberedWindowGuardedNormTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextChecks
import LogicLineages.PersistentMarking.OrdinalGuardedStageRankProof

namespace LogicLineages.PersistentMarking.NumberedWindowGuardedNormProof
open Spine NumberedWindowArithmeticAllContextTargets NumberedWindowExternalIDOperators
open NumberedWindowGuardedNormTargets NumberedWindowExternalIDOperatorChecks
open OrdinalGuardedStageRankTargets OrdinalGuardedStageRankProof

private theorem scalarLaw (S : Signature) (K : List Ty) :
    GuardedStageLaw (AddressBelow S K) (AdmittedAddress S K) (ordinalStage (scalarStep S K)) := by
  intro a n
  rw [NumberedWindowExternalIDStageProof.stageEq _ _ _ a] <;> rfl

private def scalarCalibration (S : Signature) (K : List Ty) :=
  exact_GuardedStageRank (AddressBelow S K) (AdmittedAddress S K) (ordinalStage (scalarStep S K))
    (scalarLaw S K)
    (fun _ e => (NumberedWindowArithmeticAllContextChecks.exact_AddressPathDomain S K _ _ e).2)

private theorem taggedAtScalar (S : Signature) (K : List Ty) (a : Ordinal.{0}) (n : Nat) :
    ordinalStage (taggedStep S K) a (tagScalar n) ↔ ordinalStage (scalarStep S K) a n :=
  (exact_ActualStageTagProjection ((· < ·) : Ordinal.{0} → Ordinal.{0} → Prop)
    Ordinal.lt_wf S K a n).1

theorem exact_ActualScalarStageRank : ActualScalarStageRank := by
  intro S K n a
  have standalone := (scalarCalibration S K).1 a n
  exact ⟨standalone, (taggedAtScalar S K a n).trans standalone⟩

theorem exact_ActualScalarOrdinalNorm : ActualScalarOrdinalNorm := by
  intro S K n h guard
  have scalar := (scalarCalibration S K).2.1 n h guard
  refine ⟨scalar, ⟨(taggedAtScalar S K h.rank n).mpr scalar.1, ?_⟩⟩
  intro a member
  exact scalar.2 ((taggedAtScalar S K a n).mp member)

theorem exact_IsolatedAdmittedAddressStarts : IsolatedAdmittedAddressStarts := by
  intro S K n guard isolated
  have scalar := (scalarCalibration S K).2.2 n guard isolated
  exact ⟨scalar, (taggedAtScalar S K 0 n).mpr scalar⟩

#print axioms exact_ActualScalarStageRank
#print axioms exact_ActualScalarOrdinalNorm
#print axioms exact_IsolatedAdmittedAddressStarts

end LogicLineages.PersistentMarking.NumberedWindowGuardedNormProof
