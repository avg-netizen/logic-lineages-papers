module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Frame FrameSupportProof FusionAlgebraProof
section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag ctag stag dtag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
variable (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
variable (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
variable (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
variable (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder false⟩)
include hi hl hp hr ha hc hs hd
theorem consSuccess (token raw tasks out suffix middle : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) token) (.succ middle))
  (.imp (allTasks itag ltag ptag rtag atag raw out suffix)
   (property itag ltag ptag rtag atag (HistoryLookup.consCall ctag token raw) tasks out suffix)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) token) (.succ middle)
 let P := allTasks itag ltag ptag rtag atag raw out suffix
 let H := Formula.equal (scanState itag ltag ptag rtag (HistoryLookup.consCall ctag token raw) (.succ tasks)) (.succ out)
 let G := [H,P,E]
 have he : Hilbert.Local T ctx G E := .hypothesis (by simp [G])
 have ih : Hilbert.Local T ctx G P := .hypothesis (by simp [G])
 have hh : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 obtain ⟨hfirst⟩ := StateRecursionProof.cons p itag ltag ptag rtag ctag stag hi hl hp hc hs token raw (.succ tasks)
 have hnext := scanCongruence (T := T) (G := G) itag ltag ptag rtag raw raw _ (.succ middle)
  (.base (.logical (.reflexive raw))) he
 have ht := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (localTrans _ _ _ (.base hfirst) hnext)) hh
 have hout := Hilbert.Local.mp (.mp (.base (FrameSupportProof.instanceRule itag ltag ptag rtag atag raw middle out suffix)) ih) ht
 obtain ⟨hframe⟩ := LiteralSyntaxFrame.StepProof.internalStepFrame n p stag atag ctag dtag rtag hs ha hc hd hr ctx tasks middle suffix token
 have hframed := Hilbert.Local.mp (.base hframe) he
 obtain ⟨hsecond⟩ := StateRecursionProof.cons p itag ltag ptag rtag ctag stag hi hl hp hc hs token raw (.succ (HistoryAppend.appendCall atag tasks suffix))
 have hstate := scanCongruence (T := T) (G := G) itag ltag ptag rtag raw raw _ (.succ (HistoryAppend.appendCall atag middle suffix))
  (.base (.logical (.reflexive raw))) hframed
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge
  (localTrans _ _ _ (.base hsecond) (localTrans _ _ _ hstate hout)))))⟩

omit hd in
theorem consFailure (token raw tasks out suffix : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) token) .zero)
  (.imp (allTasks itag ltag ptag rtag atag raw out suffix)
   (property itag ltag ptag rtag atag (HistoryLookup.consCall ctag token raw) tasks out suffix)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal (LiteralSyntaxStep.stepCall stag (.succ tasks) token) .zero
 let P := allTasks itag ltag ptag rtag atag raw out suffix
 let H := Formula.equal (scanState itag ltag ptag rtag (HistoryLookup.consCall ctag token raw) (.succ tasks)) (.succ out)
 let G := [H,P,E]
 have he : Hilbert.Local T ctx G E := .hypothesis (by simp [G])
 have hh : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 obtain ⟨hfirst⟩ := StateRecursionProof.cons p itag ltag ptag rtag ctag stag hi hl hp hc hs token raw (.succ tasks)
 have hnext := scanCongruence (T := T) (G := G) itag ltag ptag rtag raw raw _ .zero
  (.base (.logical (.reflexive raw))) he
 obtain ⟨hnone⟩ := NoneInductionProof.noneAll p itag ltag ptag rtag atag ctag stag hi hl hp hr ha hc hs raw
 have hz := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh)
  (localTrans _ _ _ (.base hfirst) (localTrans _ _ _ hnext (.base hnone)))
 have result := Hilbert.Local.explosion
  (.equal (scanState itag ltag ptag rtag (HistoryLookup.consCall ctag token raw) (.succ (HistoryAppend.appendCall atag tasks suffix)))
   (.succ (HistoryAppend.appendCall atag out suffix))) hz (.base (.arithmetic (.succNotZero out)))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge result)))⟩

theorem consFrame (token raw tasks out suffix : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allTasks itag ltag ptag rtag atag raw out suffix)
   (property itag ltag ptag rtag atag (HistoryLookup.consCall ctag token raw) tasks out suffix))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let e := LiteralSyntaxStep.stepCall stag (.succ tasks) token
 let Q := Formula.imp (allTasks itag ltag ptag rtag atag raw out suffix)
  (property itag ltag ptag rtag atag (HistoryLookup.consCall ctag token raw) tasks out suffix)
 obtain ⟨hz⟩ := consFailure p itag ltag ptag rtag atag ctag stag hi hl hp hr ha hc hs token raw tasks out suffix
 let P := HistoryOrder.SupportProof.predBody e
 obtain ⟨hsuc⟩ := consSuccess p itag ltag ptag rtag atag ctag stag dtag hi hl hp hr ha hc hs hd
  (liftTerm token) (liftTerm raw) (liftTerm tasks) (liftTerm out) (liftTerm suffix) (.var (0 : Fin (ctx+1)))
 have hb : Derivation T (.imp P (GorbowPACore.weaken Q)) := by
  simpa only [P,Q,e,HistoryOrder.SupportProof.predBody,GorbowPACore.weaken,substituteFormula,
   Frame.substAll,Frame.substProperty,LiteralSyntaxStep.stepCall,HistoryLookup.consCall,
   Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,renameTerm] using hsuc
 obtain ⟨he⟩ := HBQuantifier.existentialElimination T P Q ⟨hb⟩
 obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T e
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hz) he) hsplit⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameConsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameConsProof
