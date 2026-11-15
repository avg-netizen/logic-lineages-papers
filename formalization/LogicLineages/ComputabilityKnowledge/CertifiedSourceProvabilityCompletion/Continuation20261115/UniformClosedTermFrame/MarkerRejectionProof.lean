module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawRejectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.MarkerRejectionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorStepTargets
/-- The suppressed variable marker is impossible on an entire successful
closed-term scan, even when the remaining input and pending rest are arbitrary. -/
theorem marker {n ctx : Nat} (p : Program n) (stag stepTag etag ptag ctag atag l r dtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (rest tokens : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 .zero) rest)
   (HistoryLookup.consCall ctag .zero tokens)) (.succ .zero)) (.equal (.succ .zero) .zero))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let row := HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 (.zero : Term ctx)) rest
 let next := HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 2 (.zero : Term ctx)) rest
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag row (HistoryLookup.consCall ctag .zero tokens)) (.succ .zero)
 have hh : Hilbert.Local T ctx [S] S := .hypothesis List.mem_cons_self
 obtain ⟨hstep⟩ := ConstructorStepProof.stepAt p stepTag etag ptag ctag atag hst he hp hc ha (.term 0) (.zero : Term ctx) rest
 obtain ⟨hrow⟩ := UniformFixedFormulaAgreement.StackProof.appendPrefix p ctag atag hc ha
  [LiteralSyntaxStep.taskCall ptag 2 (.zero : Term ctx)] rest
 have hsucc := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (Gamma := [S]) hrow)
 have hsucc' : Hilbert.Local T ctx [S]
  (.equal (.succ (output ptag ctag atag (.term 0) .zero rest)) (.succ next)) := by
  simpa only [output,tasks,next,UniformFixedFormulaAgreement.StackProof.prepend,
   GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero,
   show (0 : Fin 6).val = 0 from rfl] using hsucc
 have hstep' : Hilbert.Local T ctx [S]
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ row) .zero) (.succ next)) := by
  simpa only [input,kind,token,Term.numeral,row] using localTrans _ _ _ (.base hstep) hsucc'
 obtain ⟨hcons⟩ := UniformSubstitutionFoldTransport.ScanProof.cons p [S] stag stepTag ptag ctag
  hs hst hp hc .zero tokens row next hstep'
 have htail := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hcons) hh
 obtain ⟨hbad⟩ := RawRejectionProof.arbitrary p stag stepTag etag ptag ctag atag l r dtag hs hst he hp hc ha hl hr hd rest tokens
 exact ⟨(Hilbert.Local.mp (.base hbad) htail).discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.MarkerRejectionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.MarkerRejectionProof
