module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation.StatementChecks

theorem composePlug : Targets.ComposePlug := Proof.composePlug

theorem composeCounts : Targets.ComposeCounts := Proof.composeCounts

theorem contextHolesLaw : Targets.ContextHolesLaw := Proof.contextHolesLaw

theorem fillCounts : Targets.FillCounts := Proof.fillCounts

theorem twoHolesLaw : Targets.TwoHolesLaw := Proof.twoHolesLaw

theorem onPathRotation : Targets.OnPathRotation := Proof.onPathRotation

theorem offPathRotation : Targets.OffPathRotation := Proof.offPathRotation

theorem occurrenceFactorization : Targets.OccurrenceFactorization := Proof.occurrenceFactorization

theorem contextDichotomy : Targets.ContextDichotomy := Proof.contextDichotomy

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation
