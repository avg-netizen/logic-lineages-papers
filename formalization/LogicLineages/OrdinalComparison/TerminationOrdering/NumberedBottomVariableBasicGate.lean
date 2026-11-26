module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableBasicGate

theorem liftImages : NumberedBottomVariableTargets.ActualLiftBottomOrVariable :=
  NumberedBottomVariableProof.actualLiftBottomOrVariable

theorem good : NumberedBottomVariableTargets.ActualBottomOrVariableGood :=
  NumberedBottomVariableProof.actualBottomOrVariableGood

theorem singleBottom : NumberedBottomVariableTargets.ActualSingleBottomOrVariable :=
  NumberedBottomVariableProof.actualSingleBottomOrVariable

theorem finiteMark : NumberedBottomVariableTargets.ActualFiniteMarkInverse :=
  NumberedBottomVariableProof.actualFiniteMarkInverse

theorem primitiveMark : NumberedBottomVariableTargets.ActualPrimitiveMarkInverse :=
  NumberedBottomVariableProof.actualPrimitiveMarkInverse

#print axioms liftImages
#print axioms good
#print axioms singleBottom
#print axioms finiteMark
#print axioms primitiveMark

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableBasicGate
