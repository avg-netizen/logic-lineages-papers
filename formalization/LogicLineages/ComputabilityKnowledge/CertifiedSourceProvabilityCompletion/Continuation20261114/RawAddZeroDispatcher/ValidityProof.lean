module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem scanWithRest {n ctx : Nat} (p : Program n) (vtag stag ptag ctag atag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (raw rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.equal (LiteralSyntaxScan.scanCall stag
    (HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag .zero) rest) raw) (.succ rest)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let one := HistoryLookup.consCall ctag task .zero
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hsound⟩ := RawReflexivityDispatcher.TermSoundProof.sound p vtag stag ptag ctag hv hs hp hc raw
 have hsingle := Hilbert.Local.mp (.base hsound) hh
 obtain ⟨hframe⟩ := LiteralSyntaxScan.FrameStatementChecks.frame n p stag atag hs ha ctx one raw .zero rest
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx task .zero rest
 have hstack := Logic.trans _ _ _ hcons
  (HistoryAppend.PositiveProof.binaryCongruence ctag task task _ rest (.logical (.reflexive task)) hnil)
 have hscanStack := HistoryAppend.PositiveProof.binaryCongruence stag _
  (HistoryLookup.consCall ctag task rest) raw raw hstack (.logical (.reflexive raw))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hscanStack))
   (localTrans _ _ _ (.mp (.base hframe) hsingle) (.base (Logic.unary (.succ (.var 0)) _ _ hnil)))))⟩

theorem internalFormulaValidity : Targets.InternalFormulaValidity := by
 intro n p vtag ftag ptag ctag atag hv hf hp hc ha ctx raw
 obtain ⟨stag,hs⟩ := TwoSol20261113.ReflexivityRecognizer.TermInternalProof.scanInstalled p vtag hv
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p ftag hf
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let task := LiteralNumeralPrefix.termTask ptag (.zero : Term ctx)
 let one := HistoryLookup.consCall ctag task .zero
 let two := HistoryLookup.consCall ctag task one
 let three := HistoryLookup.consCall ctag task two
 let zr := HistoryLookup.consCall ctag (.succ (.zero : Term ctx)) .zero
 let arg := HistoryAppend.appendCall atag raw zr
 let ar := HistoryLookup.consCall ctag (Term.numeral 3) arg
 let dup := HistoryAppend.appendCall atag ar raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hraw3⟩ := scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha raw two
 obtain ⟨hzero⟩ := LiteralNumeralPrefix.TermScanProof.scanZero p stag ptag ctag hs hp hc .zero one
 obtain ⟨hfuse1⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx three raw zr two
 have harg : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag three arg) (.succ one)) :=
  localTrans _ _ _ (.mp (.base hfuse1) (.mp (.base hraw3) hh)) (.base hzero)
 obtain ⟨hadd⟩ := LiteralTemplateQuote.TermScanProof.scanAdd p stag ptag ctag hs hp hc .zero one arg
 have har : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag two ar) (.succ one)) :=
  localTrans _ _ _ (.base hadd) harg
 obtain ⟨hraw1⟩ := scanWithRest p vtag stag ptag ctag atag hv hs hp hc ha raw .zero
 obtain ⟨hfuse2⟩ := LiteralSyntaxScan.FusionStatementChecks.exactFusion n p stag atag hs ha ctx two ar raw one
 have hdup : Hilbert.Local T ctx [H] (.equal (LiteralSyntaxScan.scanCall stag two dup) (.succ .zero)) :=
  localTrans _ _ _ (.mp (.base hfuse2) har) (.mp (.base hraw1) hh)
 obtain ⟨hequality⟩ := LiteralEqualityQuote.TermScanProof.scanEquality p stag ptag ctag hs hp hc .zero .zero dup
 have hformula := localTrans _ _ _ (.base hequality) hdup
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p ftag stag ptag ctag etag
  hf hs hp hc he .zero (RawAddZero.equalityValue ctag atag raw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hcomplete) hformula))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.ValidityProof.internalFormulaValidity
