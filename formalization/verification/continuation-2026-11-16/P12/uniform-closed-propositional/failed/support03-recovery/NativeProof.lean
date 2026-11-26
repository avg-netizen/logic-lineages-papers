module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof NativeLineProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem rawLineAccepted (isS : Bool) (a b c : List Nat)
 (ha : GorbowSyntaxValidation.validFormula 0 a = true)
 (hb : GorbowSyntaxValidation.validFormula 0 b = true)
 (hc : isS = true → GorbowSyntaxValidation.validFormula 0 c = true) :
 HistoryDispatcher.logicalFunction (Encodable.encode (nativeLine isS a b c) ::ᵥ nil) = 1 := by
 cases isS <;>
  simp_all [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
   HistoryDispatcher.truth,GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
   GorbowProofChecker.rule,GorbowProofChecker.payload,nativeLine,nativeConclusion,
   GorbowLogicalAxiomCode.compile,GorbowLogicalAxiomCode.case0,GorbowLogicalAxiomCode.case1,
   GorbowLogicalAxiomCode.guardFormulas,GorbowLogicalAxiomCode.arg]
theorem recognizedAccepted (isS : Bool) (v : List.Vector Nat 1)
 (h : evaluate (recognizer isS) v ≠ 0) : HistoryDispatcher.logicalFunction v = 1 := by
 obtain ⟨a,ha⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate firstArg v)
 obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate secondArg v)
 obtain ⟨c,hc⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate thirdArg v)
 have hl := lineAt isS firstArg secondArg thirdArg v a b c ha.symm hb.symm hc.symm
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have hfa : evaluate (formulaGuard firstArg) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula 0 a) := by
  rw [formulaGuard,twoEval,constantEval,← ha,LiteralSyntaxValidator.NativeProof.formulaEncoded]
 have hfb : evaluate (formulaGuard secondArg) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula 0 b) := by
  rw [formulaGuard,twoEval,constantEval,← hb,LiteralSyntaxValidator.NativeProof.formulaEncoded]
 have hfc : evaluate (formulaGuard thirdArg) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula 0 c) := by
  rw [formulaGuard,twoEval,constantEval,← hc,LiteralSyntaxValidator.NativeProof.formulaEncoded]
 have he : v.head = Encodable.encode (nativeLine isS a b c) := by
  by_contra hn
  simp only [recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,hl,equalEval] at h
  simp [hn] at h
 have hva : GorbowSyntaxValidation.validFormula 0 a = true := by
  by_contra hn
  cases isS <;>
   simp_all [recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_zero,equalEval,HistoryDispatcher.truth]
 have hvb : GorbowSyntaxValidation.validFormula 0 b = true := by
  by_contra hn
  cases isS <;>
   simp_all [recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_zero,equalEval,HistoryDispatcher.truth]
 have hvc : isS = true → GorbowSyntaxValidation.validFormula 0 c = true := by
  intro hs
  subst isS
  by_contra hn
  simp_all [recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_zero,equalEval,HistoryDispatcher.truth]
 rw [hv,he]
 exact rawLineAccepted isS a b c hva hvb hvc
theorem exactNativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 simp only [logicalLeaf,chooseEval,constantEval]
 by_cases hs : evaluate (recognizer true) v = 0
 · rw [if_pos hs]
   by_cases hk : evaluate (recognizer false) v = 0
   · rw [if_pos hk,hold]
   · rw [if_neg hk,recognizedAccepted false v hk]
 · rw [if_neg hs,recognizedAccepted true v hs]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.NativeProof
