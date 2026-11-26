module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.NegValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InstanceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherPrimitivesProof
theorem actualOutput {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p)
 (G : List (Formula ctx)) (matrix witness : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.fval I.vtag matrix witness)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (instanceValue I matrix witness)
   (UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag matrix witness))) := by
 obtain ⟨hgraph⟩ := UniformClosedInstanceRecognizer.StatementChecks.exactGuardedGraph n p
  I.itag I.ftag I.fval I.vtag I.ptag I.ctag I.rtag
  I.h_itag I.h_ftag I.h_fval I.h_vtag I.h_ptag I.h_ctag I.h_rtag ctx matrix witness
 have hpos := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (Hilbert.Local.base (Gamma := G) hgraph)
 have hs := Hilbert.Local.mp hpos hg
 let out := UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag matrix witness
 have hp := callCongruence I.predTag
  (UniformClosedInstanceRecognizer.instanceCall I.itag matrix witness ::ᵥ nil) (.succ out ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hs
   | succ i => exact Fin.elim0 i)
 obtain ⟨hpred⟩ := predecessor p G out I.predTag I.h_predTag
 exact ⟨localTrans _ _ _ hp hpred⟩

theorem negGuard {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p)
 (G : List (Formula ctx)) (matrix witness : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.fval I.vtag matrix witness)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.fval I.vtag (negValue I.ctag matrix) witness)) := by
 have hf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hg
 have ht := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hg
 obtain ⟨hn⟩ := NegValidityProof.unary p I G 1 1 6 matrix rfl hf
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hn) ht⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InstanceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InstanceProof
