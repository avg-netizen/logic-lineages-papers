module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionAlgebraProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Fusion

noncomputable def scanCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 (itag ltag ptag rtag : Nat) (raw raw' state state' : Term ctx)
 (hr : Hilbert.Local T ctx G (.equal raw raw'))
 (hs : Hilbert.Local T ctx G (.equal state state')) :
 Hilbert.Local T ctx G (.equal (scanState itag ltag ptag rtag raw state)
  (scanState itag ltag ptag rtag raw' state')) := by
 have ha := localUnary (scanState itag ltag ptag rtag (.var 0) (liftTerm state)) raw raw' hr
 have hb := localUnary (scanState itag ltag ptag rtag (liftTerm raw') (.var 0)) state state' hs
 simp only [substScanState,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at ha hb
 exact localTrans _ _ _ ha hb

noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat}
 (itag ltag ptag rtag atag : Nat) (left right state : Term ctx) :
 Derivation T (.imp (allFusion itag ltag ptag rtag atag left right)
  (fusion itag ltag ptag rtag atag left right state)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (fusion itag ltag ptag rtag atag (liftTerm left) (liftTerm right) (.var 0)) state)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substFusion,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,allFusion] using h

section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
variable (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)

theorem nilFusion (right state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (fusion itag ltag ptag rtag atag .zero right state)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 obtain ⟨happ⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx right
 obtain ⟨hz⟩ := StateRecursionProof.nil p itag ltag ptag rtag hi hl hp hr state
 have hleft := scanCongruence (T := T) (G := []) itag ltag ptag rtag _ right state state
  (.base happ) (.base (.logical (.reflexive state)))
 have hright := scanCongruence (T := T) (G := []) itag ltag ptag rtag right right _ state
  (.base (.logical (.reflexive right))) (.base hz)
 exact ⟨Hilbert.Local.finish (localTrans _ _ _ hleft (HistoryOrder.StepProof.localSym _ _ hright))⟩

theorem consFusion (ctag stag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (token left right state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allFusion itag ltag ptag rtag atag left right)
   (fusion itag ltag ptag rtag atag (HistoryLookup.consCall ctag token left) right state))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := allFusion itag ltag ptag rtag atag left right
 let next := LiteralSyntaxStep.stepCall stag state token
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have ih : Hilbert.Local T ctx [H] (fusion itag ltag ptag rtag atag left right next) :=
  .mp (.base (instanceRule itag ltag ptag rtag atag left right next)) hh
 obtain ⟨happ⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx token left right
 have hleft := scanCongruence (T := T) (G := [H]) itag ltag ptag rtag _ _ state state
  (.base happ) (.base (.logical (.reflexive state)))
 obtain ⟨hcons⟩ := StateRecursionProof.cons p itag ltag ptag rtag ctag stag hi hl hp hc hs token
  (HistoryAppend.appendCall atag left right) state
 obtain ⟨hsmall⟩ := StateRecursionProof.cons p itag ltag ptag rtag ctag stag hi hl hp hc hs token left state
 have hright := scanCongruence (T := T) (G := [H]) itag ltag ptag rtag right right _ _
  (.base (.logical (.reflexive right))) (.base hsmall)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hleft
  (localTrans _ _ _ (.base hcons) (localTrans _ _ _ ih (HistoryOrder.StepProof.localSym _ _ hright)))))⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionAlgebraProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionAlgebraProof
