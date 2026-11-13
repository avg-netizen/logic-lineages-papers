module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionInductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Fusion FusionAlgebraProof FusionBoundedProof HistoryBounds
section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag ctag stag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
variable (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
variable (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
variable (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)

theorem positiveAll (bound right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (boundedFusion itag ltag ptag rtag atag bound right)
   (allFusion itag ltag ptag rtag atag (.succ bound) right))) := by
 obtain ⟨h⟩ := positiveAt p itag ltag ptag rtag atag hi hl hp ha ctag stag hc hs
  (liftTerm bound) (liftTerm right) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (boundedFusion itag ltag ptag rtag atag bound right))
   (fusion itag ltag ptag rtag atag (liftTerm (.succ bound)) (liftTerm right) (.var 0))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩

theorem nextAt (bound code right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (boundedFusion itag ltag ptag rtag atag bound right)
   (.imp (weakBound code (.succ bound)) (allFusion itag ltag ptag rtag atag code right)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := boundedFusion itag ltag ptag rtag atag bound right
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := allFusion itag ltag ptag rtag atag code right
 obtain ⟨hn⟩ := positiveAll p itag ltag ptag rtag atag ctag stag hi hl hp ha hc hs bound right
 have hp0 : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hleft := Hilbert.Local.mp (.mp (.base (transportAll itag ltag ptag rtag atag (.succ bound) code right)) he)
  (.mp (.base hn) hp0)
 have hleft' : Derivation T (.imp P (.imp E Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hleft))
 have hp1 : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (boundedInstance itag ltag ptag rtag atag bound code right)) hp1) hb
 have hright' : Derivation T (.imp P (.imp B Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hright))
 let W := weakBound code (.succ bound)
 have hp2 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hsplit⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q)))
  (.mp (.base hleft') hp2)) (.mp (.base hright') hp2)) (.mp (.base hsplit) hw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

theorem next (bound right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (boundedFusion itag ltag ptag rtag atag bound right)
   (boundedFusion itag ltag ptag rtag atag (.succ bound) right))) := by
 obtain ⟨h⟩ := nextAt p itag ltag ptag rtag atag ctag stag hi hl hp ha hc hs
  (liftTerm bound) (.var (0 : Fin (ctx+1))) (liftTerm right)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (boundedFusion itag ltag ptag rtag atag bound right))
   (.imp (weakBound (.var 0) (liftTerm (.succ bound)))
    (allFusion itag ltag ptag rtag atag (.var 0) (liftTerm right)))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩

theorem fusionAll (left right state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (fusion itag ltag ptag rtag atag left right state)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := boundedFusion itag ltag ptag rtag atag (.var 0) (liftTerm right)
 obtain ⟨hz⟩ := FusionBoundedProof.base p itag ltag ptag rtag atag hi hl hp hr ha right
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p itag ltag ptag rtag atag ctag stag hi hl hp ha hc hs
  (.var (0 : Fin (ctx+1))) (liftTerm right)
 have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substBounded,substitute,successorLift,Fin.cases_zero,Support.shiftCancel] using hn
 have hall := atTerm phi left (induction phi hb hstep)
 have hbound : Derivation T (boundedFusion itag ltag ptag rtag atag left right) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hall
 have hrefl : Derivation T (weakBound left left) :=
  .mp (HistoryBounds.SupportProof.weakIntro left left .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero left)))
 have hcode := Derivation.mp (.mp (boundedInstance itag ltag ptag rtag atag left left right) hbound) hrefl
 exact ⟨.mp (instanceRule itag ltag ptag rtag atag left right state) hcode⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionInductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionInductionProof
