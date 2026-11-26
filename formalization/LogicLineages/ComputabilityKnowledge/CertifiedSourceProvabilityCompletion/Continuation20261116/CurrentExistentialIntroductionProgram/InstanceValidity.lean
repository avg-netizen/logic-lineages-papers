module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InstanceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.Definitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.InstanceValidity
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem valid {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p)
 (G : List (Formula ctx)) (a w : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.fval I.vtag a w)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (OriginalQuantifierLogicalExtension.formulaValid 0 I.fval (CurrentNegatedInstanceBridge.instanceValue I a w))) := by
 have hF := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hg
 have hV := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hg
 obtain ⟨houtput⟩ := UniformSubstitutionFormulaValidity.StatementChecks.exactFormulaOutputValidity n p
  I.ftag I.etag I.vtag I.fval I.stepTag I.stag I.ptag I.ctag I.atag I.dtag I.len I.qtag I.ltag I.rtag
  I.h_ftag I.h_etag I.h_vtag I.h_stepTag I.h_stag I.h_ptag I.h_ctag I.h_atag I.h_dtag I.h_len I.h_qtag I.h_ltag I.h_rtag I.h_fval ctx .zero a w
 have hout := Hilbert.Local.mp (Hilbert.Local.mp (.base houtput) hV) hF
 obtain ⟨he⟩ := CurrentNegatedInstanceBridge.InstanceProof.actualOutput p I G a w hg
 have hc := LiteralRawMP.DispatcherSupportProof.callCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := G) I.fval
  ((.zero : Term ctx) ::ᵥ CurrentNegatedInstanceBridge.instanceValue I a w ::ᵥ nil)
  (.zero ::ᵥ UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag a w ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive _))
   | succ i => cases i using Fin.cases with
     | zero => exact he
     | succ i => exact Fin.elim0 i)
 exact ⟨localTrans _ _ _ hc hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.InstanceValidity
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.InstanceValidity
