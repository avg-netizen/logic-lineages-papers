module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ScanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem nil {n ctx : Nat} (p : Program n) (stag ptag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (tasks : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag tasks .zero) (.succ tasks))) := by
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨hbind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr tasks (.zero : Term ctx)
 obtain ⟨hnil⟩ := LiteralSyntaxScan.StateRecursionProof.nil p itag len ptag r hi hlen hp hr (.succ tasks)
 exact ⟨Logic.trans _ _ _ hbind hnil⟩
/-- Original scanner on one actual token. Supplied step may be any installed
copy: StateRecursionProof supplies the actual defining-equation coherence. -/
theorem singleton {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (stag stepTag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (tasks token out : Term ctx)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ tasks) token) (.succ out))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag tasks (HistoryLookup.consCall ctag token .zero)) (.succ out))) := by
 obtain ⟨itag,len,ip,r,hi,hlen,_,hr⟩ := LiteralSyntaxScan.InstalledNodesProof.scanNodes p stag hs
 obtain ⟨hcons⟩ := RelationalSyntaxDepthTransport.ScanStateTransportConsProof.consAt
  p G itag len ptag r ctag stepTag hi hlen hp hc hstep token .zero tasks (.succ out) h
 obtain ⟨hnil⟩ := LiteralSyntaxScan.StateRecursionProof.nil p itag len ptag r hi hlen hp hr (.succ out)
 obtain ⟨hbind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p stag itag len ptag r hs hi hlen hp hr tasks (HistoryLookup.consCall ctag token .zero)
 exact ⟨localTrans _ _ _ (.base hbind) (localTrans _ _ _ hcons (.base hnil))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ScanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ScanProof
