module
public import LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletion.StatementChecks

theorem fullCanonicalCotree : Targets.FullCanonicalCotree := Proof.fullCanonicalCotree

end LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletion.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletion.StatementChecks
