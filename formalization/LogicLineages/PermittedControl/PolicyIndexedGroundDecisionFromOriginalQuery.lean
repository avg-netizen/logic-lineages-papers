module
public import LogicLineages.PermittedControl.PolicyIndexedGroundDecisionTargets
import LogicLineages.PermittedControl.PolicyIndexedGroundDecisionProof
import LogicLineages.PermittedControl.GroundScalarCircuitCalibrationProof
import LogicLineages.PermittedControl.GroundScalarCircuitEffectivityProof

public section
namespace LogicLineages.PermittedControl.PolicyIndexedGroundDriver
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

theorem indexedGroundFromOriginalQuery (src : IndexedSource) (hs : Partrec src) (he : SourceExact src) :
    IndexedGroundDecidable factorialControl ∧ ∀ b : Nat, IndexedGroundDecidable (nearControl b) :=
  indexedGroundFromSourceAndQuery src hs he GroundScalarCircuit.queryCode
    GroundScalarCircuit.exactQueryCode GroundScalarCircuit.queryCodeEffectivity.to_comp

#print axioms indexedGroundFromOriginalQuery
end LogicLineages.PermittedControl.PolicyIndexedGroundDriver
