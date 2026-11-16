module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.NativeAcceptance
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open OriginalQuantifierLogicalProducers
open HistoryRuleSuffix.NativeProof OriginalQuantifierLogicalProducers.NativeSupport

theorem recognizedAccepted (isExists : Bool) (v : List.Vector Nat 1)
 (h : evaluate (recognizer isExists) v ≠ 0) : HistoryDispatcher.logicalFunction v = 1 := by
 obtain ⟨a,ha⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate firstArg v)
 obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate secondArg v)
 have hl := lineAt isExists firstArg secondArg v a b ha.symm hb.symm
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have he : v.head = Encodable.encode (nativeLine isExists a b) := by
  by_contra hn
  simp only [recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,hl,equalEval] at h
  simp [hn] at h
 have hg : evaluate (if isExists then formulaGuard 1 firstArg
  else conjunction (formulaGuard 0 firstArg) (formulaGuard 0 secondArg)) v ≠ 0 := by
  intro hz
  apply h
  rw [recognizer,conjunctionEval,hz]
  split <;> rfl
 have hgValid : if isExists then GorbowSyntaxValidation.validFormula 1 a = true
  else GorbowSyntaxValidation.validFormula 0 a = true ∧ GorbowSyntaxValidation.validFormula 0 b = true := by
  cases isExists with
  | true => exact NativeAcceptance.validOfNonzero 1 firstArg v a ha.symm hg
  | false =>
   have hfirst : evaluate (formulaGuard 0 firstArg) v ≠ 0 := by
    intro hz
    apply hg
    change evaluate (conjunction (formulaGuard 0 firstArg) (formulaGuard 0 secondArg)) v = 0
    rw [conjunctionEval,hz,if_pos rfl]
   have hsecond : evaluate (formulaGuard 0 secondArg) v ≠ 0 := by
    simpa only [Bool.false_eq_true,if_false,conjunctionEval,if_neg hfirst] using hg
   exact ⟨NativeAcceptance.validOfNonzero 0 firstArg v a ha.symm hfirst,
    NativeAcceptance.validOfNonzero 0 secondArg v b hb.symm hsecond⟩
 rw [hv,he]
 exact NativeAcceptance.rawAccepted isExists a b hgValid

theorem exactNative : Targets.Native := by
 constructor
 · intro old v
   simp only [logicalLeaf,chooseEval,constantEval]
 · intro old hold v
   simp only [logicalLeaf,chooseEval,constantEval]
   by_cases hd : evaluate (recognizer true) v = 0
   · rw [if_pos hd]
     by_cases hc : evaluate (recognizer false) v = 0
     · rw [if_pos hc,hold]
     · rw [if_neg hc,recognizedAccepted false v hc]
   · rw [if_neg hd,recognizedAccepted true v hd]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.NativeProof
