module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitutionValidity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitutionValidity.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem localScan (t : Term 1) {n ctx : Nat} (p : Program n) (vtag stag ptag ctag atag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (raw rest : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [RawReflexivityDispatcher.valid vtag raw]
 (.equal (LiteralSyntaxScan.scanCall stag
  (HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag .zero) rest)
  (RawUnarySubstitution.value ctag atag raw t)) (.succ rest))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 induction t generalizing rest with
 | var i =>
  obtain ⟨h⟩ := RawAddZeroDispatcher.ValidityProof.scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha raw rest
  exact ⟨.mp (.base h) hh⟩
 | zero =>
  obtain ⟨h⟩ := LiteralNumeralPrefix.TermScanProof.scanZero p stag ptag ctag hs hp hc .zero rest
  exact ⟨.base h⟩
 | succ t ih =>
  obtain ⟨h⟩ := ih rest
  obtain ⟨hstep⟩ := LiteralNumeralPrefix.TermScanProof.scanSucc p stag ptag ctag hs hp hc .zero rest (RawUnarySubstitution.value ctag atag raw t)
  exact ⟨localTrans _ _ _ (.base hstep) h⟩
 | add t u ht hu =>
  let one := HistoryLookup.consCall ctag task rest
  let two := HistoryLookup.consCall ctag task one
  obtain ⟨hl⟩ := ht one
  obtain ⟨hr⟩ := hu rest
  obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two
   (RawUnarySubstitution.value ctag atag raw t) (RawUnarySubstitution.value ctag atag raw u) one
  have happ := localTrans _ _ _ (.mp (.base hfuse) hl) hr
  obtain ⟨hstep⟩ := LiteralTemplateQuote.TermScanProof.scanAdd p stag ptag ctag hs hp hc .zero rest
   (HistoryAppend.appendCall atag (RawUnarySubstitution.value ctag atag raw t) (RawUnarySubstitution.value ctag atag raw u))
  exact ⟨localTrans _ _ _ (.base hstep) happ⟩
 | mul t u ht hu =>
  let one := HistoryLookup.consCall ctag task rest
  let two := HistoryLookup.consCall ctag task one
  obtain ⟨hl⟩ := ht one
  obtain ⟨hr⟩ := hu rest
  obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two
   (RawUnarySubstitution.value ctag atag raw t) (RawUnarySubstitution.value ctag atag raw u) one
  have happ := localTrans _ _ _ (.mp (.base hfuse) hl) hr
  obtain ⟨hstep⟩ := LiteralTemplateQuote.TermScanProof.scanMul p stag ptag ctag hs hp hc .zero rest
   (HistoryAppend.appendCall atag (RawUnarySubstitution.value ctag atag raw t) (RawUnarySubstitution.value ctag atag raw u))
  exact ⟨localTrans _ _ _ (.base hstep) happ⟩
 | universalFunction t ih =>
  obtain ⟨h⟩ := ih rest
  obtain ⟨hstep⟩ := LiteralTemplateQuote.TermScanProof.scanUniversal p stag ptag ctag hs hp hc .zero rest (RawUnarySubstitution.value ctag atag raw t)
  exact ⟨localTrans _ _ _ (.base hstep) h⟩

theorem internalScan : Targets.InternalScan := by
 intro t n p vtag stag ptag ctag atag hv hs hp hc ha ctx raw rest
 obtain ⟨h⟩ := localScan t p vtag stag ptag ctag atag hv hs hp hc ha raw rest
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

theorem internalValidity : Targets.InternalValidity := by
 intro t n p vtag stag ptag ctag atag hv hs hp hc ha ctx raw
 obtain ⟨hscan⟩ := localScan t p vtag stag ptag ctag atag hv hs hp hc ha raw .zero
 obtain ⟨h⟩ := RawSuccCongruence.ValidityProof.localBinding p [RawReflexivityDispatcher.valid vtag raw]
  vtag stag ptag ctag hv hs hp hc (RawUnarySubstitution.value ctag atag raw t) hscan
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitutionValidity.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitutionValidity.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitutionValidity.Proof.localScan
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitutionValidity.Proof.internalScan
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitutionValidity.Proof.internalValidity
