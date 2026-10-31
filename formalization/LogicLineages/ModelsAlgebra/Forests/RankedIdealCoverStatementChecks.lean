module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCover.StatementChecks
 theorem nonlinearExact : Targets.NonlinearExact := Proof.nonlinearExact
 theorem piecesCorrect : Targets.PiecesCorrect := Proof.piecesCorrect
 theorem coverCorrect : Targets.CoverCorrect := Proof.coverCorrect
 theorem emptyExact : Targets.EmptyExact := Proof.emptyExact
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCover.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCover
