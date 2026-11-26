module
public import LogicLineages.CartierObserverCurrent.FullSelectedCoefficientTargets
public import LogicLineages.OrdinalComparison.BinaryObserverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullSelectedCoefficient
open LogicLineages.OrdinalComparison

theorem completeSelectedCoefficient : Targets.CompleteSelectedCoefficient := by
  refine ⟨actualBinaryInitialVectorCalibration, ?_, ?_⟩
  · exact actualBinaryMatrixWordProduct (ZMod 2)
  · exact actualSourceBinarySelectedParity

#audit_namespace LogicLineages.CartierObserverCurrent.FullSelectedCoefficient
end LogicLineages.CartierObserverCurrent.FullSelectedCoefficient
