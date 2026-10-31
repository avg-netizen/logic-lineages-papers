module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode.StatementChecks
 theorem framesExact : Targets.FramesExact := Proof.framesExact
 theorem seedsIdeal : Targets.SeedsIdeal := Proof.seedsIdeal
 theorem seedsSound : Targets.SeedsSound := Proof.seedsSound
 theorem entriesCovered : Targets.EntriesCovered := Proof.entriesCovered
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode
