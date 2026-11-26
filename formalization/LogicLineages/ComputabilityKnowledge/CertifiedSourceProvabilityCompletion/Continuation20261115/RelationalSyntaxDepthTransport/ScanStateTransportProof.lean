module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds
open ScanStateTransportSupportProof ScanStateTransportBoundProof

theorem base {n ctx : Nat} (p : Program n) (itag len ptag q l r : Nat)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (bounded (ctx := ctx) itag len ptag q l r .zero)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term (ctx+1) := .var 0
 let H := weakBound code .zero
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hz⟩ := ScanStateTransportRawProof.nilAll (ctx := ctx+1) p itag len ptag q l r hi hlen hp hr
 have hcode := HistoryOrder.StepProof.localSym _ _ (.mp (.base he) hh)
 have hout := Hilbert.Local.mp (.mp (.base (transportAll itag len ptag q l r .zero code)) hcode) (.base hz)
 exact ⟨.generalize hout.discharge.finish⟩

theorem nextAt {n ctx : Nat} (p : Program n) (itag stag etag ptag ctag atag len q l r : Nat)
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
 (bound code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag len ptag q l r bound)
   (.imp (weakBound code (.succ bound)) (allStacks itag len ptag q l r code)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := bounded itag len ptag q l r bound
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := allStacks itag len ptag q l r code
 obtain ⟨hn⟩ := ScanStateTransportRawProof.positive p itag stag etag ptag ctag atag len q l r
  hi hs he hp hc ha hlen hq hl hr bound
 have hp0 : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he0 : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hleft := Hilbert.Local.mp (.mp (.base (transportAll itag len ptag q l r (.succ bound) code)) he0) (.mp (.base hn) hp0)
 have hleft' : Derivation T (.imp P (.imp E Q)) := hleft.discharge.discharge.finish
 have hp1 : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (boundedInstance itag len ptag q l r bound code)) hp1) hb
 have hright' : Derivation T (.imp P (.imp B Q)) := hright.discharge.discharge.finish
 let W := weakBound code (.succ bound)
 have hp2 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hsplit⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q)))
  (.mp (.base hleft') hp2)) (.mp (.base hright') hp2)) (.mp (.base hsplit) hw)
 exact ⟨hout.discharge.discharge.finish⟩

theorem next {n ctx : Nat} (p : Program n) (itag stag etag ptag ctag atag len q l r : Nat)
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
 (bound : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag len ptag q l r bound) (bounded itag len ptag q l r (.succ bound)))) := by
 obtain ⟨h⟩ := nextAt p itag stag etag ptag ctag atag len q l r hi hs he hp hc ha hlen hq hl hr
  (liftTerm bound) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (bounded itag len ptag q l r bound))
   (.imp (weakBound (.var 0) (liftTerm (.succ bound))) (allStacks itag len ptag q l r (.var 0)))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩
/-- Internal PA induction over the raw-code bound; all changing coordinates
remain quantified in the invariant. This is the original iterator, not reflection. -/
theorem scanStateTransport : ScanStateTransportTargets.InternalScanStateTransport := by
 intro n p itag stag etag ptag ctag atag len q l r hi hs he hp hc ha hlen hq hl hr ctx raw ot nt result
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := bounded itag len ptag q l r (.var 0)
 obtain ⟨hz⟩ := base (ctx := ctx) p itag len ptag q l r hi hlen hp hr
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p itag stag etag ptag ctag atag len q l r hi hs he hp hc ha hlen hq hl hr (.var (0 : Fin (ctx+1)))
 have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substBounded,substitute,Fin.cases_zero] using hn
 have hall := atTerm phi raw (induction phi hb hstep)
 have hbound : Derivation T (bounded itag len ptag q l r raw) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,Fin.cases_zero] using hall
 have hrefl : Derivation T (weakBound raw raw) :=
  .mp (HistoryBounds.SupportProof.weakIntro raw raw .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero raw)))
 have hstacks := Derivation.mp (.mp (boundedInstance itag len ptag q l r raw raw) hbound) hrefl
 exact ⟨.mp (instanceRule itag len ptag q l r raw ot nt result) hstacks⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ScanStateTransportProof
