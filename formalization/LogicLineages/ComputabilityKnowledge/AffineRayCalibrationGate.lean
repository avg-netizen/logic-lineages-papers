module

public import LogicLineages.ComputabilityKnowledge.AffineRayCalibrationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem affine_ray_calibration : Comparators.AffineRayCalibration.Target :=
  AffineRayCalibrationProof.affineRayCalibration

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
