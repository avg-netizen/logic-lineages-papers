module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.AcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open AcceptanceProof
theorem exactInternalLogical : Targets.InternalLogical := by
 intro n p old isS qtag ltag ptag ctag atag fval hq hl hp hc ha hf ctx a b c
 obtain ⟨hline⟩ := ConstructorProof.exactInternalLine n p isS qtag ptag ctag atag hq hp hc ha ctx a b c
 obtain ⟨haccept⟩ := rawAcceptanceImp p old isS ltag ptag ctag atag fval hl hp hc ha hf a b c
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 let T := GorbowPRNumeralCalculation.Theory p
 let A := guards isS fval a b c
 have hA : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (.base haccept) hA
 have hout := localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.LogicalProof
