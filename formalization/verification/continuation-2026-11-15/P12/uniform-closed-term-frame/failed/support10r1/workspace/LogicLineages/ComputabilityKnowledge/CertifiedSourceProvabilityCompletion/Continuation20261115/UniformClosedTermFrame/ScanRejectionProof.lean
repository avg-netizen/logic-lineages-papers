module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.IndexZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ScanRejectionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport LiteralRawMP.DispatcherSupportProof
/-- A closed complete scan cannot be waiting for an index at bound zero. -/
def claim {ctx : Nat} (stag ptag ctag : Nat) (rest tokens : Term ctx) : Formula ctx :=
 .imp (.equal (LiteralSyntaxScan.scanCall stag
  (HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 2 .zero) rest) tokens) (.succ .zero))
  (.equal (.succ .zero) .zero)
theorem substClaim {m n : Nat} (s : Fin m → Term n) stag ptag ctag (rest tokens : Term m) :
 substituteFormula s (claim stag ptag ctag rest tokens) =
 claim stag ptag ctag (substitute s rest) (substitute s tokens) := by
 simp only [claim,substituteFormula,LiteralSyntaxScan.scanCall,HistoryLookup.DropEquationsProof.substCons,
  LiteralSyntaxStep.taskCall,HistoryKernel.pairCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
  LiteralSyntaxStep.ExpansionSupportProof.substituteNumeral,substitute]
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} stag ptag ctag (rest a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (claim stag ptag ctag rest a) (claim stag ptag ctag rest b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (claim stag ptag ctag (liftTerm rest) (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substClaim,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

theorem nil {n ctx : Nat} (p : Program n) (stag ptag ctag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (claim stag ptag ctag rest .zero)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let task : Term ctx := LiteralSyntaxStep.taskCall ptag 2 .zero
 let row := HistoryLookup.consCall ctag task rest
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag row .zero) (.succ .zero)
 have hh : Hilbert.Local T ctx [S] S := .hypothesis List.mem_cons_self
 obtain ⟨hn⟩ := UniformSubstitutionChunkTransport.ScanProof.nil p stag ptag hs hp row
 have he := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _)))
  (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hn)) hh)
 obtain ⟨hcns⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx task rest
 have hz := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hcns)) he
 have hout := Hilbert.Local.explosion (.equal (.succ .zero) .zero) hz (.base (.arithmetic (.succNotZero _)))
 exact ⟨hout.discharge.finish⟩

theorem cons {n ctx : Nat} (p : Program n) (stag stepTag etag ptag ctag atag l r dtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (rest token tail : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (claim stag ptag ctag rest (HistoryLookup.consCall ctag token tail))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let row := HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 2 (.zero : Term ctx)) rest
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag row (HistoryLookup.consCall ctag token tail)) (.succ .zero)
 have hh : Hilbert.Local T ctx [S] S := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := IndexZeroProof.stepZero p stepTag etag ptag ctag l r dtag hst he hp hc hl hr hd rest token
 obtain ⟨hout⟩ := UniformSubstitutionFoldTransport.ScanProof.reject p [S] stag stepTag ptag ctag atag
  hs hst hp hc ha token tail row .zero (.equal (.succ .zero) .zero) (.base hz) hh
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ScanRejectionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.ScanRejectionProof
