module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine.StatementChecks
 theorem entrySound : Targets.EntrySound := Proof.entrySound
 theorem frameSound : Targets.FrameSound := Proof.frameSound
 theorem linearSpineExact : Targets.LinearSpineExact := Proof.linearSpineExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine
