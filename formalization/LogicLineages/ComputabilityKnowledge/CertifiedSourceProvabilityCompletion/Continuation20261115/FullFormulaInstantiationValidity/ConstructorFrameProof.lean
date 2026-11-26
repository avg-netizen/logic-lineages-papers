module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorFrameProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof ConstructorValidityTargets
/-- Actual singleton task framing, with append equations discharged internally. -/
theorem frameOne {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (stag ctag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (task raw suffix : Term ctx)
 (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) raw) (.succ .zero))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (HistoryLookup.consCall ctag task suffix) raw) (.succ suffix))) := by
 obtain ⟨hframe⟩ := LiteralSyntaxScan.FrameProof.internalFrame n p stag atag hs ha ctx (singleton ctag task) raw .zero suffix
 have hframed := Hilbert.Local.mp (.base hframe) hvalid
 obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx task .zero suffix
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx suffix
 have htail := callCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := G) ctag (task ::ᵥ HistoryAppend.appendCall atag .zero suffix ::ᵥ nil)
  (task ::ᵥ suffix ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact Hilbert.Local.base (.logical (.reflexive task))
   | succ i => cases i using Fin.cases with
     | zero => exact .base hnil
     | succ i => exact Fin.elim0 i)
 have htasks := localTrans _ _ _ (.base hcons) htail
 have hinput := callCongruence stag (HistoryAppend.appendCall atag (singleton ctag task) suffix ::ᵥ raw ::ᵥ nil)
  (HistoryLookup.consCall ctag task suffix ::ᵥ raw ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact htasks
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive raw))
     | succ i => exact Fin.elim0 i)
 have hout := localUnary (.succ (.var 0)) _ _ (Hilbert.Local.base (Gamma := G) hnil)
 have hout' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (.succ (HistoryAppend.appendCall atag .zero suffix)) (.succ suffix)) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hout
 exact ⟨localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hinput) (localTrans _ _ _ hframed hout')⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorFrameProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorFrameProof
