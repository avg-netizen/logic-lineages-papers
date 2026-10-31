module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotreeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree.StatementChecks

theorem reducedComponents : Targets.ReducedComponents := Proof.reducedComponents

theorem reducedUniqueness : Targets.ReducedUniqueness := Proof.reducedUniqueness

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree
