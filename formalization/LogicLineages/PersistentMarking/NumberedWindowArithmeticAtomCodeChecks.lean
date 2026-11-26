import LogicLineages.PersistentMarking.NumberedWindowArithmeticHeadCodeProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderCodeProof
import LogicLineages.PersistentMarking.NumberedWindowFiniteBinderProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks
open NumberedWindowArithmeticAtomCodeTargets NumberedWindowArithmeticBinderCode

theorem exact_TyFuelCalibration : TyFuelCalibration :=
  NumberedWindowArithmeticTyCodeProof.calibration

theorem exact_TyCodec : ExactTyCodec :=
  NumberedWindowArithmeticTyCodeProof.exactCodec

theorem exact_HeadCodec : ExactHeadCodec :=
  NumberedWindowArithmeticHeadCodeProof.exactCodec

theorem exact_BinderFuelCalibration : BinderFuelCalibration :=
  NumberedWindowArithmeticBinderCodeProof.calibration

theorem exact_BinderCodec : ExactBinderCodec :=
  NumberedWindowArithmeticBinderCodeProof.exactCodec

theorem exact_CodedOriginalBinderLookup : CodedOriginalBinderLookup := by
  intro Γ i
  unfold codedLookup
  rw [NumberedWindowArithmeticBinderCodeProof.roundtrip Γ]
  exact congrFun (NumberedWindowFiniteBinderProof.lookup Γ) i

#print axioms exact_TyFuelCalibration
#print axioms exact_TyCodec
#print axioms exact_HeadCodec
#print axioms exact_BinderFuelCalibration
#print axioms exact_BinderCodec
#print axioms exact_CodedOriginalBinderLookup

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks
