module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.AcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open OriginalQuantifierLogicalProducers
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem exactInternalLogical : Targets.InternalLogical := by
 intro n p old isExists qtag ltag ptag ctag atag fval hq hl hp hc ha hf ctx a b
 obtain ⟨hline⟩ := OriginalQuantifierLogicalProducers.LineGraph.lineAt p [] ptag ctag atag hp hc ha isExists
  (.projection 0) (.projection 1) (a ::ᵥ b ::ᵥ nil) a b
  (projection p [] _ 0) (projection p [] _ 1) qtag hq
 obtain ⟨haccept⟩ := AcceptanceProof.rawAcceptanceImp p old isExists ltag ptag ctag atag fval hl hp hc ha hf a b
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ (Hilbert.Local.finish hline)
 let T := GorbowPRNumeralCalculation.Theory p
 let A := guards isExists fval a b
 have hA : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (.base haccept) hA
 have hout := localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.LogicalProof
