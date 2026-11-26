module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameInductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Frame FrameSupportProof FrameBoundedProof HistoryBounds
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
theorem positiveAll (bound out suffix : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag ltag ptag rtag atag bound out suffix)
   (allTasks itag ltag ptag rtag atag (.succ bound) out suffix))) := by
 obtain ⟨h⟩ := positiveAt p itag ltag ptag rtag atag hi hl hp hr ha ctag stag dtag hc hs hd
  (liftTerm bound) (.var (0 : Fin (ctx+1))) (liftTerm out) (liftTerm suffix)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (bounded itag ltag ptag rtag atag bound out suffix))
   (property itag ltag ptag rtag atag (liftTerm (.succ bound)) (.var 0) (liftTerm out) (liftTerm suffix))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩

theorem nextAt (bound code out suffix : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag ltag ptag rtag atag bound out suffix)
   (.imp (weakBound code (.succ bound)) (allTasks itag ltag ptag rtag atag code out suffix)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := bounded itag ltag ptag rtag atag bound out suffix
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := allTasks itag ltag ptag rtag atag code out suffix
 obtain ⟨hn⟩ := positiveAll p itag ltag ptag rtag atag ctag stag dtag hi hl hp hr ha hc hs hd bound out suffix
 have hp0 : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hleft := Hilbert.Local.mp (.mp (.base (transportAll itag ltag ptag rtag atag (.succ bound) code out suffix)) he)
  (.mp (.base hn) hp0)
 have hleft' : Derivation T (.imp P (.imp E Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hleft))
 have hp1 : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (boundedInstance itag ltag ptag rtag atag bound code out suffix)) hp1) hb
 have hright' : Derivation T (.imp P (.imp B Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hright))
 let W := weakBound code (.succ bound)
 have hp2 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hsplit⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q)))
  (.mp (.base hleft') hp2)) (.mp (.base hright') hp2)) (.mp (.base hsplit) hw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

theorem next (bound out suffix : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag ltag ptag rtag atag bound out suffix)
   (bounded itag ltag ptag rtag atag (.succ bound) out suffix))) := by
 obtain ⟨h⟩ := nextAt p itag ltag ptag rtag atag ctag stag dtag hi hl hp hr ha hc hs hd
  (liftTerm bound) (.var (0 : Fin (ctx+1))) (liftTerm out) (liftTerm suffix)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (bounded itag ltag ptag rtag atag bound out suffix))
   (.imp (weakBound (.var 0) (liftTerm (.succ bound)))
    (allTasks itag ltag ptag rtag atag (.var 0) (liftTerm out) (liftTerm suffix)))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩

include hr
theorem frameAll (left tasks out suffix : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property itag ltag ptag rtag atag left tasks out suffix)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := bounded itag ltag ptag rtag atag (.var 0) (liftTerm out) (liftTerm suffix)
 obtain ⟨hz⟩ := FrameBoundedProof.base p itag ltag ptag rtag atag hi hl hp hr out suffix
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p itag ltag ptag rtag atag ctag stag dtag hi hl hp hr ha hc hs hd
  (.var (0 : Fin (ctx+1))) (liftTerm out) (liftTerm suffix)
 have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substBounded,substitute,successorLift,Fin.cases_zero,Support.shiftCancel] using hn
 have hall := atTerm phi left (induction phi hb hstep)
 have hbound : Derivation T (bounded itag ltag ptag rtag atag left out suffix) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hall
 have hrefl : Derivation T (weakBound left left) :=
  .mp (HistoryBounds.SupportProof.weakIntro left left .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero left)))
 have hcode := Derivation.mp (.mp (boundedInstance itag ltag ptag rtag atag left left out suffix) hbound) hrefl
 exact ⟨.mp (instanceRule itag ltag ptag rtag atag left tasks out suffix) hcode⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameInductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameInductionProof
