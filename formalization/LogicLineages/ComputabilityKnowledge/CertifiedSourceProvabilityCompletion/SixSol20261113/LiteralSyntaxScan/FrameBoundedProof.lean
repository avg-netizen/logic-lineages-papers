module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameBoundedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Frame FrameSupportProof HistoryBounds
noncomputable def transportProperty {T : Sentence → Prop} {ctx : Nat} itag ltag ptag rtag atag (a b tasks out suffix : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property itag ltag ptag rtag atag a tasks out suffix) (property itag ltag ptag rtag atag b tasks out suffix))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property itag ltag ptag rtag atag (.var 0) (liftTerm tasks) (liftTerm out) (liftTerm suffix)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
variable (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
include hi hl hp hr
theorem nilAll (out suffix : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (allTasks itag ltag ptag rtag atag .zero out suffix)) := by
 obtain ⟨h⟩ := nilFrame p itag ltag ptag rtag atag hi hl hp hr (.var (0 : Fin (ctx+1))) (liftTerm out) (liftTerm suffix)
 exact ⟨.generalize h⟩
theorem base (out suffix : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (bounded itag ltag ptag rtag atag .zero out suffix)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term (ctx+1) := .var 0
 let H := weakBound code .zero
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hz⟩ := nilAll p itag ltag ptag rtag atag hi hl hp hr (liftTerm out) (liftTerm suffix)
 have hcode := HistoryOrder.StepProof.localSym _ _ (.mp (.base he) hh)
 have hout := Hilbert.Local.mp (.mp (.base (transportAll itag ltag ptag rtag atag .zero code (liftTerm out) (liftTerm suffix))) hcode) (.base hz)
 exact ⟨.generalize (Hilbert.Local.finish (Hilbert.Local.discharge hout))⟩
include ha
theorem positiveAt (ctag stag dtag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (count tasks out suffix : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (bounded itag ltag ptag rtag atag count out suffix)
  (property itag ltag ptag rtag atag (.succ count) tasks out suffix))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := bounded itag ltag ptag rtag atag count out suffix
 let vt := HistoryAppend.PositiveProof.valueAt atag
 let ht := HistoryAppend.PositiveProof.inputHeadTag atag
 let tt := HistoryAppend.PositiveProof.inputTailTag atag
 let head := call ht (.succ count ::ᵥ nil)
 let tail := call tt (.succ count ::ᵥ nil)
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨_,hhead,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p vt hv
 obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p tt htail ctx count
 obtain ⟨he⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag ht tt hc hhead htail ctx count
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have ih := Hilbert.Local.mp (.mp (.base (boundedInstance itag ltag ptag rtag atag count tail out suffix)) hh) (.base hb)
 obtain ⟨hcns⟩ := FrameConsProof.consFrame p itag ltag ptag rtag atag ctag stag dtag hi hl hp hr ha hc hs hd head tail tasks out suffix
 have hout := Hilbert.Local.mp (.mp (.base (transportProperty itag ltag ptag rtag atag (HistoryLookup.consCall ctag head tail) (.succ count) tasks out suffix)) (.base he)) (.mp (.base hcns) ih)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameBoundedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameBoundedProof
