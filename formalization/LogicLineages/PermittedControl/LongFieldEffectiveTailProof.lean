module
public import LogicLineages.PermittedControl.LongFieldEffectiveTailTargets
import LogicLineages.PermittedControl.LongFieldTailPrimitiveProof
import LogicLineages.PermittedControl.LongFieldTailCalibrationProof
import LogicLineages.PermittedControl.LongFieldDistinctBoundProof
import LogicLineages.PermittedControl.LongFieldSameBoundProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison

theorem longFieldTailEffective : LongFieldTailEffective :=
  ⟨omegaMultipleTailCode_primrec, longFieldPeelBoundCode_primrec,
    longFieldDistinctBoundCode_primrec, longFieldSameBoundCode_primrec,
    omegaMultipleTailCode_calibrated, longFieldPeelBoundCode_calibrated,
    longFieldTailCodes_calibrated⟩

theorem fullLongFieldEffectiveTail : FullLongFieldEffectiveTail :=
  ⟨longFieldTailEffective, longFieldDistinctAtBound, longFieldSameAtBound⟩

end LogicLineages.PermittedControl.FieldComparison
