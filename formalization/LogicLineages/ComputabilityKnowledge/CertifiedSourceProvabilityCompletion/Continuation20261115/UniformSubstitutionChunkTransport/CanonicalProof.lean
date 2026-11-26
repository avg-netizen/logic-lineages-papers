module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.ConstructorProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.MarkerProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CanonicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport.ConstructorStepTargets
def newOutput {ctx : Nat} (ptag ctag atag : Nat) (ctor : Constructor) (depth tail : Term ctx) : Term ctx :=
 HistoryAppend.appendCall atag (FinitePrefixTargets.prefixTerm ctag (RowProof.newRows ptag depth ctor)) tail
theorem appendOne {n ctx : Nat} (p : Program n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (head tail : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall atag (HistoryLookup.consCall ctag head .zero) tail)
   (HistoryLookup.consCall ctag head tail))) := by
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx head .zero tail
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx tail
 have htail := LiteralRawMP.DispatcherSupportProof.callCongruence
  (T := GorbowPRNumeralCalculation.Theory p) (G := []) ctag
  (head ::ᵥ HistoryAppend.appendCall atag .zero tail ::ᵥ List.Vector.nil)
  (head ::ᵥ tail ::ᵥ List.Vector.nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive head))
   | succ i => cases i using Fin.cases with
     | zero => exact .base hnil
     | succ i => exact Fin.elim0 i)
 exact ⟨Logic.trans _ _ _ hcons htail.finish⟩
theorem allConstructors {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (etag stepTag stag ptag ctag atag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ctor : Constructor) (depth oldTail newTail raw : Term ctx)
 (hrest : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r oldTail newTail)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (resultBody stag len q l r
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) depth) newTail)
   (UniformClosedSubstitutionEmit.emitCall etag
    (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral (kind ctor)) (.succ depth) oldTail)
    (Term.numeral (token ctor)) raw)
   (output ptag ctag atag ctor (.succ depth) oldTail)
   (newOutput ptag ctag atag ctor depth newTail))) := by
 classical
 by_cases hm : ctor = .term 0
 · subst ctor
   obtain ⟨hmark⟩ := MarkerProof.marker p G etag stag ptag ctag len q l r he hs hp hc hlen hq hl hr depth oldTail newTail raw hrest
   have hscan := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hmark
   obtain ⟨hnew⟩ := appendOne p ctag atag hc ha (LiteralSyntaxStep.taskCall ptag 0 depth) newTail
   have hsucc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
    (.equal (.succ (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 depth) newTail))
     (.succ (newOutput ptag ctag atag (.term 0) depth newTail))) :=
    localUnary (.succ (.var 0)) _ _ (.base (Support.equalitySymmetry _ _ hnew))
   have hs' := localTrans _ _ _ hscan hsucc
   have hrows := RowProof.rows p G ptag l r hp hl hr (.term 0) depth
   obtain ⟨hrel⟩ := FinitePrefixProof.finitePrefixAppend n p len q l r ctag atag hlen hq hc ha ctx G
    (tasks ptag (.succ depth) (.term 0)) (RowProof.newRows ptag depth (.term 0)) oldTail newTail hrows ⟨hrest⟩
   have hrel' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
    (stackRelation len q l r (output ptag ctag atag (.term 0) (.succ depth) oldTail)
     (newOutput ptag ctag atag (.term 0) depth newTail)) := by
    simpa only [output,newOutput,ConstructorProof.prefixSame] using hrel
   exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hs') hrel'⟩
 · obtain ⟨h⟩ := ConstructorProof.nonMarker p G etag stepTag stag ptag ctag atag len q l r
    he hstep hs hp hc ha hlen hq hl hr ctor hm depth oldTail newTail raw hrest
   simpa only [newOutput,ConstructorProof.rowsUnchanged ptag depth ctor hm,ConstructorProof.prefixSame,output] using (Nonempty.intro h)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CanonicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CanonicalProof
