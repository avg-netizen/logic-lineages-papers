module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierOperationalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralSyntaxStep

def tasks {ctx : Nat} (ptag ctag : Nat) (binder : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (taskCall ptag 1 binder) .zero

theorem singletonAppendNil {n ctx : Nat} (p : Program n) (atag ctag : Nat)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (task : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (HistoryAppend.appendCall atag (HistoryLookup.consCall ctag task .zero) .zero)
  (HistoryLookup.consCall ctag task .zero))) := by
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx task .zero .zero
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx (.zero : Term ctx)
 exact ⟨Logic.trans _ _ _ hcons (HistoryAppend.PositiveProof.binaryCongruence ctag task task _ .zero (.logical (.reflexive task)) hnil)⟩

theorem quantifierStep {n ctx : Nat} (p : Program n) (stag etag atag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) (i : Fin 2) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (stepCall stag (.succ (tasks ptag ctag binder)) (Term.numeral (10+i.val)))
  (.succ (tasks ptag ctag (.succ binder))))) := by
 obtain ⟨hexpand⟩ := ExpansionProof.internalQuantifier n p etag ptag ctag he hp hc ctx binder i
 obtain ⟨hstep⟩ := StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (taskCall ptag 1 binder) .zero (Term.numeral (10+i.val)) (tasks ptag ctag (.succ binder))
 obtain ⟨hnil⟩ := singletonAppendNil p atag ctag ha hc (taskCall ptag 1 (.succ binder))
 exact ⟨Logic.trans _ _ _ (.mp hstep hexpand) (Logic.unary (.succ (.var 0)) _ _ hnil)⟩

theorem scanConsSuccess {n ctx : Nat} (p : Program n) (scanTag itag ltag ptag rtag ctag stag : Nat)
 (hscan : (nodes p)[scanTag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hi : (nodes p)[itag]? = some ⟨2,LiteralSyntaxScan.iterator⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (stack added token raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (stepCall stag (.succ stack) token) (.succ added))
  (.equal (LiteralSyntaxScan.scanCall scanTag stack (HistoryLookup.consCall ctag token raw))
   (LiteralSyntaxScan.scanCall scanTag added raw)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (stepCall stag (.succ stack) token) (.succ added)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hbind⟩ := LiteralSyntaxScan.ScanBindingProof.binding p scanTag itag ltag ptag rtag hscan hi hl hp hr stack (HistoryLookup.consCall ctag token raw)
 obtain ⟨hcons⟩ := LiteralSyntaxScan.StateRecursionProof.cons p itag ltag ptag rtag ctag stag hi hl hp hc hs token raw (.succ stack)
 have hstate := LiteralSyntaxScan.FusionAlgebraProof.scanCongruence (T := T) (G := [H]) itag ltag ptag rtag raw raw _ (.succ added)
  (.base (.logical (.reflexive raw))) hh
 obtain ⟨hfinal⟩ := LiteralSyntaxScan.ScanBindingProof.binding p scanTag itag ltag ptag rtag hscan hi hl hp hr added raw
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hbind)
  (localTrans _ _ _ (.base hcons) (localTrans _ _ _ hstate (.base (Support.equalitySymmetry _ _ hfinal))))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierOperationalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierOperationalProof
