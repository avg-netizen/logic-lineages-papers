module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ScanRejectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawRejectionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open ScanRejectionProof
theorem positive {n ctx : Nat} (p : Program n) (stag stepTag etag ptag ctag atag l r dtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (rest count : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (claim stag ptag ctag rest (.succ count))) := by
 let vt := HistoryAppend.PositiveProof.valueAt atag
 let ht := HistoryAppend.PositiveProof.inputHeadTag atag
 let tt := HistoryAppend.PositiveProof.inputTailTag atag
 let head := call ht (.succ count ::ᵥ nil)
 let tail := call tt (.succ count ::ᵥ nil)
 have hval := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨_,hhead,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p vt hval
 obtain ⟨heq⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag ht tt hc hhead htail ctx count
 obtain ⟨hcns⟩ := ScanRejectionProof.cons p stag stepTag etag ptag ctag atag l r dtag
  hs hst he hp hc ha hl hr hd rest head tail
 exact ⟨.mp (.mp (transport stag ptag ctag rest (HistoryLookup.consCall ctag head tail) (.succ count)) heq) hcns⟩

/-- Exhausts arbitrary internal raw codes using genuine original list reconstruction. -/
theorem arbitrary {n ctx : Nat} (p : Program n) (stag stepTag etag ptag ctag atag l r dtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (rest tokens : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (claim stag ptag ctag rest tokens)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Z := Formula.equal tokens .zero
 let H := HistoryOrder.SupportProof.predBody tokens
 let Q := claim stag ptag ctag rest tokens
 obtain ⟨hn⟩ := ScanRejectionProof.nil p stag ptag ctag hs hp hc rest
 have hz : Hilbert.Local T ctx [Z] Z := .hypothesis List.mem_cons_self
 have hzero := Hilbert.Local.mp (.mp (.base (transport stag ptag ctag rest .zero tokens))
  (HistoryOrder.StepProof.localSym _ _ hz)) (.base hn)
 obtain ⟨hpos⟩ := positive p stag stepTag etag ptag ctag atag l r dtag
  hs hst he hp hc ha hl hr hd (liftTerm rest) (.var (0 : Fin (ctx+1)))
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 have hpositive := Hilbert.Local.mp (.mp (.base (transport stag ptag ctag (liftTerm rest)
  (.succ (.var 0)) (liftTerm tokens))) (HistoryOrder.StepProof.localSym _ _ hh)) (.base hpos)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  rw [show Q = claim stag ptag ctag rest tokens from rfl,GorbowPACore.weaken,substClaim]
  simpa only [liftTerm,renameTerm] using hpositive.discharge.finish
 obtain ⟨hex⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T tokens
 exact ⟨.mp (.mp (.mp (.logical (.orElim Z (.ex H) Q)) hzero.discharge.finish) hex) hcases⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawRejectionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawRejectionProof
