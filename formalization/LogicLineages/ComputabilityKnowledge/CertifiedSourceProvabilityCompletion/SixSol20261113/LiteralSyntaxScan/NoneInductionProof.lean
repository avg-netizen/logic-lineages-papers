module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneInductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds NoneSupportProof
section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag ctag stag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
variable (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
variable (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
variable (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
include hi hl hp ha hc hs

theorem nextAt (bound code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag ltag ptag rtag bound)
   (.imp (weakBound code (.succ bound)) (property itag ltag ptag rtag code)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := bounded itag ltag ptag rtag bound
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := property itag ltag ptag rtag code
 obtain ⟨hn⟩ := positive p itag ltag ptag rtag atag ctag stag hi hl hp ha hc hs bound
 have hp0 : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hleft := Hilbert.Local.mp (.mp (.base (transport itag ltag ptag rtag (.succ bound) code)) he) (.mp (.base hn) hp0)
 have hleft' : Derivation T (.imp P (.imp E Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hleft))
 have hp1 : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (instanceRule itag ltag ptag rtag bound code)) hp1) hb
 have hright' : Derivation T (.imp P (.imp B Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hright))
 let W := weakBound code (.succ bound)
 have hp2 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hsplit⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have hout := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q)))
  (.mp (.base hleft') hp2)) (.mp (.base hright') hp2)) (.mp (.base hsplit) hw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

theorem next (bound : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag ltag ptag rtag bound) (bounded itag ltag ptag rtag (.succ bound)))) := by
 obtain ⟨h⟩ := nextAt p itag ltag ptag rtag atag ctag stag hi hl hp ha hc hs
  (liftTerm bound) (.var (0 : Fin (ctx+1)))
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (bounded itag ltag ptag rtag bound))
   (.imp (weakBound (.var 0) (liftTerm (.succ bound))) (property itag ltag ptag rtag (.var 0)))) := by
  simpa only [GorbowPACore.weaken,substBounded,liftTerm,renameTerm,substitute] using h
 exact ⟨HistoryIteratorSuffix.RelationProof.universalUnder _ _ h'⟩

include hr
theorem noneAll (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property itag ltag ptag rtag raw)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let phi : Formula (ctx+1) := bounded itag ltag ptag rtag (.var 0)
 obtain ⟨hz⟩ := NoneSupportProof.base (ctx := ctx) p itag ltag ptag rtag hi hl hp hr
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,Fin.cases_zero] using hz
 obtain ⟨hn⟩ := next p itag ltag ptag rtag atag ctag stag hi hl hp ha hc hs (.var (0 : Fin (ctx+1)))
 have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substBounded,substitute,Fin.cases_zero] using hn
 have hall := atTerm phi raw (induction phi hb hstep)
 have hbound : Derivation T (bounded itag ltag ptag rtag raw) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substBounded,substitute,Fin.cases_zero] using hall
 have hrefl : Derivation T (weakBound raw raw) :=
  .mp (HistoryBounds.SupportProof.weakIntro raw raw .zero) (Support.equalitySymmetry _ _ (.arithmetic (.addZero raw)))
 exact ⟨.mp (.mp (instanceRule itag ltag ptag rtag raw raw) hbound) hrefl⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneInductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneInductionProof
