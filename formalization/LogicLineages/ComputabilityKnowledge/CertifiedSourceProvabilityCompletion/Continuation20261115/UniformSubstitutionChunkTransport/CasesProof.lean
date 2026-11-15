module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawConstructorProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.GapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport.ConstructorStepTargets RelationalSyntaxDepthTransport.ExpansionCasesTargets
open RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- All19 successful raw expansion arms are eliminated internally. Neither a
constructor choice nor an index positivity witness is assumed in the result. -/
theorem classified {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (etag vtag stepTag xtag stag ptag ctag atag dtag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nh nt tok result added raw : Term ctx)
 (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid vtag raw))
 (hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (taskRelation l r oh nh))
 (htail : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r ot nt))
 (hex : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.expandCall xtag oh tok) (.succ added)))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (results stag len q l r (HistoryLookup.consCall ctag nh nt)
   (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag oh ot)) tok raw) result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := results stag len q l r (HistoryLookup.consCall ctag nh nt)
  (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag oh ot)) tok raw) result
 have hctors : ∀ ctor, Nonempty (Hilbert.Local T ctx G (.imp (constructorCase ptag ctag l r oh tok added ctor) Q)) := by
  intro ctor
  let C := constructorCase ptag ctag l r oh tok added ctor
  have hcase : Hilbert.Local T ctx (C :: G) C := .hypothesis List.mem_cons_self
  have hk := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcase
  have hb := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hcase
  have ht := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hb
  obtain ⟨hout⟩ := RawConstructorProof.transport p (C :: G) etag stepTag stag ptag ctag atag len q l r
   he hstep hs hp hc ha hlen hq hl hr ctor oh ot nh nt tok result raw
   (push C hh) (push C htail) hk ht (push C hold)
  exact ⟨hout.discharge⟩
 let I := indexCase dtag l r oh tok added
 have hi : Hilbert.Local T ctx (I :: G) I := .hypothesis List.mem_cons_self
 have hk := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hi
 have hb := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hi
 have hg := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hb
 obtain ⟨helim⟩ := GapProof.eliminate p etag vtag stepTag stag ptag ctag atag dtag len q l r
  he hv hstep hs hp hc ha hd hl hr oh ot nh nt tok result raw
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.mp (.base helim) hg) (push I hvalid))
  (push I hh)) (push I htail)) hk) (push I hold)
 obtain ⟨hall⟩ := RelationalSyntaxDepthTransport.StepTransportCasesProof.foldCases
  constructors (constructorCase ptag ctag l r oh tok added) I Q hctors hout.discharge
 obtain ⟨hclass⟩ := RelationalSyntaxDepthTransport.ExpansionCasesProof.expansionSuccessCases
  n p xtag ptag ctag dtag l r hx hp hc hd hl hr ctx oh tok added
 exact ⟨.mp hall (.mp (.base hclass) hex)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CasesProof
