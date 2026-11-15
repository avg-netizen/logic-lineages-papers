module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Genuine success-preserving original cons scan recursion, arbitrary tails. -/
theorem cons {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (stag stepTag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (token tokens oldTasks middle : Term ctx)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token) (.succ middle))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag oldTasks (HistoryLookup.consCall ctag token tokens))
   (LiteralSyntaxScan.scanCall stag middle tokens))) := by
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨hcons⟩ := RelationalSyntaxDepthTransport.ScanStateTransportConsProof.consAt p G itag len ptag r ctag stepTag
  hi hlen hp hc hstep token tokens oldTasks (.succ middle) h
 obtain ⟨hl⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr oldTasks
  (HistoryLookup.consCall ctag token tokens)
 obtain ⟨ht⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr middle tokens
 exact ⟨localTrans _ _ _ (.base hl) (localTrans _ _ _ hcons (.base (Support.equalitySymmetry _ _ ht)))⟩
/-- A rejecting first old step contradicts complete old scan success, using
original NONE propagation rather than an extra intermediate-success premise. -/
theorem reject {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (stag stepTag ptag ctag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (token tokens oldTasks oldResult : Term ctx) (Q : Formula ctx)
 (hz : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token) .zero))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag oldTasks (HistoryLookup.consCall ctag token tokens)) (.succ oldResult))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G Q) := by
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨hbind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr oldTasks
  (HistoryLookup.consCall ctag token tokens)
 have hstate := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hbind)) hold
 exact RelationalSyntaxDepthTransport.ScanStateTransportConsProof.rejectZero p G itag len ptag r atag ctag stepTag
  hi hlen hp hr ha hc hstep token tokens oldTasks oldResult Q hz hstate
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.ScanProof
