module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierOperationalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.ImplicationOperationalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralSyntaxStep QuantifierOperationalProof

def doubleTasks {ctx : Nat} (ptag ctag : Nat) (binder : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (taskCall ptag 1 binder) (tasks ptag ctag binder)

theorem implicationStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (stepCall stag (.succ (tasks ptag ctag binder)) (Term.numeral 7))
  (.succ (doubleTasks ptag ctag binder)))) := by
 obtain ⟨hexpand⟩ := ExpansionProof.internalFormulaBinary n p etag ptag ctag he hp hc ctx binder (0 : Fin 3)
 obtain ⟨hstep⟩ := StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (taskCall ptag 1 binder) .zero (Term.numeral 7) (doubleTasks ptag ctag binder)
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx
  (taskCall ptag 1 binder) (tasks ptag ctag binder) .zero
 obtain ⟨hnil⟩ := singletonAppendNil p atag ctag ha hc (taskCall ptag 1 binder)
 have hlast := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ _ (.logical (.reflexive (taskCall ptag 1 binder))) hnil
 have hout := Logic.trans _ _ _ hcons hlast
 exact ⟨Logic.trans _ _ _ (.mp hstep hexpand) (Logic.unary (.succ (.var 0)) _ _ hout)⟩

theorem doubledPrefix {n ctx : Nat} (p : Program n) (scanTag atag ptag ctag : Nat)
 (hscan : (nodes p)[scanTag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder antecedent : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralSyntaxScan.scanCall scanTag (tasks ptag ctag binder) antecedent) (.succ .zero))
  (.equal (LiteralSyntaxScan.scanCall scanTag (doubleTasks ptag ctag binder) antecedent)
   (.succ (tasks ptag ctag binder))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let single := tasks ptag ctag binder
 let H := Formula.equal (LiteralSyntaxScan.scanCall scanTag single antecedent) (.succ .zero)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hframe⟩ := LiteralSyntaxScan.FrameProof.internalFrame n p scanTag atag hscan ha ctx single antecedent .zero single
 have hf := Hilbert.Local.mp (.base hframe) hh
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx (taskCall ptag 1 binder) .zero single
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx single
 have hdouble := Logic.trans _ _ _ hcons (HistoryAppend.PositiveProof.binaryCongruence ctag _ _ _ single
  (.logical (.reflexive (taskCall ptag 1 binder))) hnil)
 have hscanEq := HistoryAppend.PositiveProof.binaryCongruence scanTag _ (doubleTasks ptag ctag binder) antecedent antecedent hdouble (.logical (.reflexive antecedent))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hscanEq))
  (localTrans _ _ _ hf (localUnary (.succ (.var 0)) _ _ (.base hnil)))))⟩

theorem scanConclusion {n ctx : Nat} (p : Program n) (scanTag itag ltag ptag rtag ctag stag etag atag : Nat)
 (hscan : (nodes p)[scanTag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (binder antecedent conclusion : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralSyntaxScan.scanCall scanTag (tasks ptag ctag binder) antecedent) (.succ .zero))
  (.imp (.equal (LiteralSyntaxScan.scanCall scanTag (tasks ptag ctag binder) (binaryRaw atag ctag 7 antecedent conclusion)) (.succ .zero))
   (.equal (LiteralSyntaxScan.scanCall scanTag (tasks ptag ctag binder) conclusion) (.succ .zero))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let single := tasks ptag ctag binder
 let double := doubleTasks ptag ctag binder
 let A := Formula.equal (LiteralSyntaxScan.scanCall scanTag single antecedent) (.succ .zero)
 let I := Formula.equal (LiteralSyntaxScan.scanCall scanTag single (binaryRaw atag ctag 7 antecedent conclusion)) (.succ .zero)
 have hA : Hilbert.Local T ctx [I,A] A := .hypothesis (by simp)
 have hI : Hilbert.Local T ctx [I,A] I := .hypothesis List.mem_cons_self
 obtain ⟨hpref⟩ := doubledPrefix p scanTag atag ptag ctag hscan ha hc binder antecedent
 have hprefix := Hilbert.Local.mp (.base hpref) hA
 obtain ⟨hstep⟩ := implicationStep p stag etag atag ptag ctag hs he ha hp hc binder
 obtain ⟨hunroll⟩ := scanConsSuccess p scanTag itag ltag ptag rtag ctag stag hscan hi hl hp hr hc hs
  single double (Term.numeral 7) (HistoryAppend.appendCall atag antecedent conclusion)
 have hscanEq := Derivation.mp hunroll hstep
 obtain ⟨hfuse⟩ := LiteralSyntaxScan.FusionProof.internalFusion n p scanTag atag hscan ha ctx double antecedent conclusion single
 have hjoined := Hilbert.Local.mp (.base hfuse) hprefix
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (localTrans _ _ _ (.base hscanEq) hjoined)) hI)))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.ImplicationOperationalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.ImplicationOperationalProof
