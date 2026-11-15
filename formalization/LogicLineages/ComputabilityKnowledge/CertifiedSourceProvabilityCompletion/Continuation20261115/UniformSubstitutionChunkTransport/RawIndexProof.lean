module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.PairProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.IndexProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawIndexProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralRawMP.DispatcherSupportProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Raw successful index arm; actual positive difference witness is consumed,
not a native index bound. Its existential elimination follows separately. -/
theorem transport {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (etag vtag stepTag stag ptag ctag atag dtag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nh nt tok result raw gap : Term ctx)
 (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid vtag raw))
 (hrel : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (taskRelation l r oh nh))
 (hrest : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r ot nt))
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (call l (oh ::ᵥ nil)) (Term.numeral 2)))
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (HistoryDifference.differenceCall dtag tok (call r (oh ::ᵥ nil))) (.succ gap)))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (results stag len q l r (HistoryLookup.consCall ctag nh nt)
   (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag oh ot)) tok raw) result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let depth := call r (nh ::ᵥ nil)
 obtain ⟨hkind⟩ := KindProof.index T l r oh nh
 have hnewkind := Hilbert.Local.mp (.mp (.base hkind) hrel) hk
 obtain ⟨hpairs⟩ := PairProof.canonical p G ptag l r 2 0 hp hl hr oh nh hrel hk hnewkind
 have ho := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hpairs
 have hn := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hpairs
 have hot := TransportProof.cons ctag _ _ ot ho
 have hnt := TransportProof.cons ctag _ _ nt hn
 have hb := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrel
 have hdiff := callCongruence (T := T) (G := G) dtag
  (tok ::ᵥ call r (oh ::ᵥ nil) ::ᵥ nil) (tok ::ᵥ .succ depth ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive tok))
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 have hnewgap := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hdiff) hg
 obtain ⟨xtag,hx⟩ := RelationalSyntaxDepthTransport.ClosedScanInstallationProof.expandNode p stepTag hstep
 obtain ⟨hindex⟩ := RelationalSyntaxDepthTransport.StepTransportIndexProof.indexStep
  p G stepTag xtag ctag atag dtag l r hstep hx hc ha hd hl hr oh ot tok gap hk hg
 have hsucc := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hold) hindex
 have hresult := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) hsucc
 have hemit := TransportProof.emit etag _ _ tok tok raw hot (.base (.logical (.reflexive tok)))
 obtain ⟨hbody⟩ := IndexProof.framed p G etag vtag stag ptag ctag atag dtag len q l r
  he hv hs hp hc ha hd tok depth gap ot nt raw hvalid hnewgap hrest
 exact TransportProof.finishCanonical stag len q l r _ _ _ _ result ot nt hnt hemit hresult hbody
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawIndexProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawIndexProof
