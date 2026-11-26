module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepInstallationProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags SixSol20261113 SixSol20261112.Fuel HistoryRuleSuffix LiteralSyntaxStep

/-- The first original kind equality test already contains the same literal
difference AST used by the index test. Registry coherence permits this copy;
no new program is installed and no index-path membership is assumed. -/
theorem originalDifferenceInstalled : StepSuccessTargets.OriginalDifferenceInstalled := by
 intro n p etag he
 let no := whenEqual kind 1 formulaBranch (whenEqual kind 2 indexBranch (constant 2 0))
 let test := applyTwo equalCode kind (constant 2 0)
 let outerArgs := Fin.cases test (Fin.cases no (Fin.cases termBranch Fin.elim0))
 have ht := Equations.argumentChild p etag HistoryCodec.select outerArgs he 0
 let ttag := etag + argumentTag HistoryCodec.select outerArgs 0
 let eqArgs := Fin.cases kind (Fin.cases (constant 2 0) Fin.elim0)
 have hq := Equations.functionChild p ttag equalCode eqArgs ht
 let qtag := ttag+1
 let inner := choose (applyTwo HistoryCodec.difference (.projection 1) (.projection 0))
  (constant 2 1) (constant 2 0)
 let qArgs := Fin.cases HistoryCodec.difference (Fin.cases inner (Fin.cases (constant 2 0) Fin.elim0))
 have hd := Equations.argumentChild p qtag HistoryCodec.select qArgs hq 0
 exact ⟨qtag + argumentTag HistoryCodec.select qArgs 0,hd⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepInstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepInstallationProof
