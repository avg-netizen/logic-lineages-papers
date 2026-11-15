module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportOldStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportRawProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open ScanStateTransportSupportProof ScanStateTransportBoundProof
/-- Three applications of the original universal rule keep EVERY changing stack
and result coordinate internally bound while retaining only the raw-bound IH. -/
noncomputable def generalizeStacks {T : Sentence → Prop} {ctx : Nat} itag len ptag q l r
 (H : Formula ctx) (raw : Term ctx)
 (h : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken H)))
  (property itag len ptag q l r (liftTerm (liftTerm (liftTerm raw))) (.var 2) (.var 1) (.var 0)))) :
 Derivation T (.imp H (allStacks itag len ptag q l r raw)) := by
 have h1 := HistoryIteratorSuffix.RelationProof.universalUnder _ _ h
 have h1' : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken H))
  (allResults itag len ptag q l r (liftTerm (liftTerm raw)) (.var (1 : Fin (ctx+2))) (.var 0))) := by
  simpa only [allResults,liftTerm,renameTerm,substitute,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] using h1
 have h2 := HistoryIteratorSuffix.RelationProof.universalUnder _ _ h1'
 have h2' : Derivation T (.imp (GorbowPACore.weaken H)
  (allNew itag len ptag q l r (liftTerm raw) (.var (0 : Fin (ctx+1))))) := by
  simpa only [allNew,liftTerm,renameTerm,substitute,Fin.succ_zero_eq_one] using h2
 exact HistoryIteratorSuffix.RelationProof.universalUnder _ _ h2'
/-- Original empty-input transport with all three coordinates generalized. -/
theorem nilAll {n ctx : Nat} (p : Program n) (itag len ptag q l r : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (allStacks (ctx := ctx) itag len ptag q l r .zero)) := by
 obtain ⟨h⟩ := ScanStateTransportSupportProof.nil (ctx := ctx+3) p itag len ptag q l r hi hlen hp hr (.var 2) (.var 1) (.var 0)
 exact ⟨.generalize (.generalize (.generalize h))⟩
/-- Full cons transport, now universally generalized over both stacks and result. -/
theorem consAll {n ctx : Nat} (p : Program n) (itag stag etag ptag ctag atag len q l r : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (token raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allStacks itag len ptag q l r raw)
   (allStacks itag len ptag q l r (HistoryLookup.consCall ctag token raw)))) := by
 let H := allStacks itag len ptag q l r raw
 obtain ⟨h⟩ := ScanStateTransportOldStepProof.cons (ctx := ctx+3) p itag stag etag ptag ctag atag len q l r
  hi hs he hp hc ha hlen hq hl hr (liftTerm (liftTerm (liftTerm token))) (liftTerm (liftTerm (liftTerm raw)))
  (.var 2) (.var 1) (.var 0)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken H)))
   (property itag len ptag q l r (liftTerm (liftTerm (liftTerm (HistoryLookup.consCall ctag token raw))))
    (.var 2) (.var 1) (.var 0))) := by
  simpa only [H,GorbowPACore.weaken,substAllStacks,ScanStateTransportOldStepProof.consClaim,
   liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons] using h
 exact ⟨generalizeStacks itag len ptag q l r H (HistoryLookup.consCall ctag token raw) h'⟩
/-- Positive arbitrary raw code is reconstructed by actual original head/tail
programs. Their internal tail bound supplies the genuine course-of-values IH. -/
theorem positive {n ctx : Nat} (p : Program n) (itag stag etag ptag ctag atag len q l r : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (count : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag len ptag q l r count) (allStacks itag len ptag q l r (.succ count)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := bounded itag len ptag q l r count
 let vt := HistoryAppend.PositiveProof.valueAt atag
 let ht := HistoryAppend.PositiveProof.inputHeadTag atag
 let tt := HistoryAppend.PositiveProof.inputTailTag atag
 let head := call ht (.succ count ::ᵥ nil)
 let tail := call tt (.succ count ::ᵥ nil)
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨_,hhead,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p vt hv
 obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p tt htail ctx count
 obtain ⟨heq⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag ht tt hc hhead htail ctx count
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hih := Hilbert.Local.mp (.mp (.base (boundedInstance itag len ptag q l r count tail)) hh) (.base hb)
 obtain ⟨hcns⟩ := consAll p itag stag etag ptag ctag atag len q l r hi hs he hp hc ha hlen hq hl hr head tail
 have hrow := Hilbert.Local.mp (.base hcns) hih
 have hout := Hilbert.Local.mp (.mp (.base (transportAll itag len ptag q l r
  (HistoryLookup.consCall ctag head tail) (.succ count))) (.base heq)) hrow
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportRawProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportRawProof
