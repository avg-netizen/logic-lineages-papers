module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanInstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralSyntaxScan.StateRecursionProof LiteralSyntaxScan.Fusion
/-- Empty old final stack forces the new final witness to be empty, internally.
No native length evaluation or encoded-stack image assumption is used. -/
theorem emptyResult {n ctx : Nat} (p : Program n) (itag len ptag q l r ctag : Nat)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (raw tasks : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (ScanStateTransportTargets.witnesses itag len ptag q l r raw tasks .zero)
   (.equal (scanState itag len ptag r raw (.succ tasks)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := ScanStateTransportTargets.witnessBody itag len ptag q l r (liftTerm raw) (liftTerm tasks) .zero (.var (0 : Fin (ctx+1)))
 let Q := Formula.equal (scanState itag len ptag r raw (.succ tasks)) (.succ .zero)
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 have hs := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 obtain ⟨he⟩ := LengthZeroProof.relatedEmpty p len q l r ctag hlen hc (.var (0 : Fin (ctx+1)))
 have hz := Hilbert.Local.mp (.base he) hrel
 have hsucc := localUnary (.succ (.var 0)) _ _ hz
 have hsucc' : Hilbert.Local T (ctx+1) [H] (.equal (.succ (.var 0)) (.succ .zero)) := by
  simpa only [GorbowStandardInstances.instantiate,substitute,Fin.cases_zero] using hsucc
 have hout := localTrans _ _ _ hs hsucc'
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,GorbowPACore.weaken,substituteFormula,substScanState,substitute,liftTerm,renameTerm] using hout.discharge.finish
 exact HBQuantifier.existentialElimination T H Q ⟨hb⟩
/-- Exact ORIGINAL frozen relational scanner theorem, with every auxiliary node
recovered inside the same registry and the supplied relation tags preserved. -/
theorem closedScanTransport : Targets.InternalClosedScanTransport := by
 intro n p scanTag len q ptag ctag atag l r hscan hlen hq hp hc ha hl hr ctx tasks newTasks raw
 obtain ⟨itag,il,ip,ir,hi,_,_,_⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p scanTag hscan
 obtain ⟨stag,hs⟩ := LiteralSyntaxScan.InstalledNodesProof.stepNode p itag hi
 obtain ⟨etag,he⟩ := ClosedScanInstallationProof.expandNode p stag hs
 obtain ⟨holdBind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p scanTag itag len ptag r hscan hi hlen hp hr tasks raw
 obtain ⟨hnewBind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p scanTag itag len ptag r hscan hi hlen hp hr newTasks raw
 obtain ⟨htransport⟩ := ScanStateTransportProof.scanStateTransport n p itag stag etag ptag ctag atag len q l r
  hi hs he hp hc ha hlen hq hl hr ctx raw tasks newTasks .zero
 obtain ⟨hempty⟩ := emptyResult p itag len ptag q l r ctag hlen hc raw newTasks
 let T := GorbowPRNumeralCalculation.Theory p
 let R := stackRelation len q l r tasks newTasks
 let S := Formula.equal (LiteralSyntaxScan.scanCall scanTag tasks raw) (.succ .zero)
 let G := [S,R]
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 have hstate := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ holdBind)) hold
 have hw := Hilbert.Local.mp (.mp (.base htransport) hrel) hstate
 have hnewState := Hilbert.Local.mp (.base hempty) hw
 have hout := localTrans _ _ _ (.base hnewBind) hnewState
 exact ⟨hout.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanProof
