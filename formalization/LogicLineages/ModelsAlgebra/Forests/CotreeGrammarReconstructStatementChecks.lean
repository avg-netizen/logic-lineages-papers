module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstructProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct.StatementChecks

theorem forestReconstruction : Targets.ForestReconstruction := Proof.forestReconstruction

theorem wordReconstruction : Targets.WordReconstruction := Proof.wordReconstruction

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct
