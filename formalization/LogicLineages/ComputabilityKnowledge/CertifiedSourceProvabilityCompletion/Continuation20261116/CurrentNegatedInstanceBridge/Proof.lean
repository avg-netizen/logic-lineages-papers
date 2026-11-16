module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.OutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem exactInternal : Targets.Internal := by
 intro n p I ctx matrix witness
 let T := GorbowPRNumeralCalculation.Theory p
 let H := UniformClosedInstanceRecognizer.guards I.fval I.vtag matrix witness
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 obtain ⟨hng⟩ := InstanceProof.negGuard p I G matrix witness hh
 obtain ⟨hi⟩ := InstanceProof.actualOutput p I G matrix witness hh
 obtain ⟨hni⟩ := InstanceProof.actualOutput p I G (negValue I.ctag matrix) witness hng
 obtain ⟨hout⟩ := OutputProof.negatedOutput p I matrix witness
 have hneg := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ctag
  (Term.numeral 6) _ (Term.numeral 6) _ (.base (.logical (.reflexive _)))
  (HistoryOrder.StepProof.localSym _ _ hi)
 have hresult := localTrans _ _ _ (.base hout) hneg
 have hcommute := localTrans _ _ _ hni hresult
 obtain ⟨hcase⟩ := UniformClosedRule13Validity.GraphProof.exactConclusionGraph n p I.toGraphInstallation ctx
  (negValue I.ctag matrix) witness
 have hc := Hilbert.Local.mp (.base hcase) hng
 let allNeg := FixedFormulaSubstitution.unaryValue I.ctag 10 (negValue I.ctag matrix)
 have happ := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.atag
  allNeg _ allNeg _ (.base (.logical (.reflexive _))) hresult
 have hshape := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := G) I.ctag
  (Term.numeral 7) _ (Term.numeral 7) _ (.base (.logical (.reflexive _))) happ
 have hconclusion := localTrans _ _ _ hc hshape
 have hboth := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hcommute) hconclusion
 exact ⟨hboth.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.Proof
