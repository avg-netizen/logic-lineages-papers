module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanPreflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanInstallationProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags
open SixSol20261113 SixSol20261112.Fuel HistoryRuleSuffix
/-- Recover the literal original expansion node inside the actual step, without
adding any installation premise or extending the registry. -/
theorem expandNode {n : Nat} (p : Program n) (stag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩) :
 ∃ etag : Nat, (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩ := by
 let g2 : Fin 3 → Program 2 := Fin.cases LiteralSyntaxStep.expanded
  (Fin.cases (constant 2 0) (Fin.cases (LiteralSyntaxStep.success LiteralSyntaxStep.appended) Fin.elim0))
 let inner : Program 2 := choose LiteralSyntaxStep.expanded (constant 2 0) (LiteralSyntaxStep.success LiteralSyntaxStep.appended)
 let g1 : Fin 3 → Program 2 := Fin.cases LiteralSyntaxStep.stack
  (Fin.cases (constant 2 0) (Fin.cases inner Fin.elim0))
 let middle : Program 2 := choose LiteralSyntaxStep.stack (constant 2 0) inner
 let g0 : Fin 3 → Program 2 := Fin.cases (.projection 0)
  (Fin.cases (constant 2 0) (Fin.cases middle Fin.elim0))
 have hmiddle := Equations.argumentChild p stag HistoryCodec.select g0 hs 2
 let mtag := stag + argumentTag HistoryCodec.select g0 2
 have hinner := Equations.argumentChild p mtag HistoryCodec.select g1 hmiddle 2
 let xtag := mtag + argumentTag HistoryCodec.select g1 2
 have hexpanded := Equations.argumentChild p xtag HistoryCodec.select g2 hinner 0
 let etag := xtag + argumentTag HistoryCodec.select g2 0
 let args : Fin 2 → Program 2 := Fin.cases LiteralSyntaxStep.headTask (Fin.cases (.projection 1) Fin.elim0)
 exact ⟨etag+1,Equations.functionChild p etag LiteralSyntaxStep.expandCode args hexpanded⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanInstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanInstallationProof
