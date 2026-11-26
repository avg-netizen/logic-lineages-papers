module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem internalMultiplicationValidity : Targets.InternalMultiplicationValidity := by
 intro n p vtag ptag ctag atag hv hp hc ha ctx t u
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p vtag hv
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag t
 let K := RawReflexivityDispatcher.valid vtag u
 let G := [K,H]
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let one := HistoryLookup.consCall ctag task .zero
 let two := HistoryLookup.consCall ctag task one
 have ht : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hu : Hilbert.Local T ctx G K := .hypothesis List.mem_cons_self
 obtain ⟨htwo⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha t one
 obtain ⟨hone⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha u .zero
 obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two t u one
 have happ := localTrans _ _ _ (.mp (.base hfuse) (.mp (.base htwo) ht)) (.mp (.base hone) hu)
 obtain ⟨hadd⟩ := LiteralTemplateQuote.TermScanProof.scanMul p stag ptag ctag hs hp hc .zero .zero (HistoryAppend.appendCall atag t u)
 have hscan := localTrans _ _ _ (.base hadd) happ
 obtain ⟨hout⟩ := RawSuccCongruence.ValidityProof.localBinding p G vtag stag ptag ctag hv hs hp hc (mulRaw ctag atag t u) hscan
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.ValidityProof.internalMultiplicationValidity
