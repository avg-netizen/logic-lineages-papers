module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.NativeLineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof NativeLineProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open TwoSol20261113.ReflexivityRecognizer
/-- Acceptance by the ORIGINAL logical checker follows from its actual compile13
and instanceCode guards, not from an assumption about the new recognizer. -/
theorem rawLineAccepted (a b c : List Nat)
 (ha : GorbowSyntaxValidation.validFormula 1 a = true)
 (hb : GorbowSyntaxValidation.validTerm 0 b = true)
 (hc : GorbowSyntaxValidation.validTerm 0 c = true) :
 HistoryDispatcher.logicalFunction (Encodable.encode (nativeLine a b c) ::ᵥ nil) = 1 := by
 let left := GorbowSubstitutionCode.subRaw 1 1 0 [b] a
 let right := GorbowSubstitutionCode.subRaw 1 1 0 [c] a
 let result := GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 0 b c)
  (GorbowCodeConstructors.binary 7 left right)
 have hl : GorbowInstanceCode.instanceCode 0 a b = some left := by
  simp [GorbowInstanceCode.instanceCode,GorbowInstanceCode.variableDictionary,
   GorbowSubstitutionCode.substituteFormulaCode,GorbowLiftedDictionary.dictionaryValid,ha,hb,left]
 have hr : GorbowInstanceCode.instanceCode 0 a c = some right := by
  simp [GorbowInstanceCode.instanceCode,GorbowInstanceCode.variableDictionary,
   GorbowSubstitutionCode.substituteFormulaCode,GorbowLiftedDictionary.dictionaryValid,ha,hc,right]
 have hcase : GorbowLogicalAxiomCode.case12 0 [a,b,c] = some result := by
  rw [UniformClosedCase12.NativeCasesProof.originalTriple,hl,hr]
  rfl
 have hcompile : GorbowLogicalAxiomCode.compile 0 (12,[a,b,c]) = some result := by
  simp [GorbowLogicalAxiomCode.compile,hcase]
 simp [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,nativeLine,HistoryDispatcher.truth,hcase,hcompile]
/-- Original function calibration for EVERY numeric line, retaining the old
fallback verbatim on all unmatched or malformed inputs. -/
theorem exactNativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 obtain ⟨a,ha⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate termCode v)
 obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate RawAddSucc.secondTermCode v)
 obtain ⟨c,hc⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate thirdTermCode v)
 have hl := lineAt termCode RawAddSucc.secondTermCode thirdTermCode v a b c ha.symm hb.symm hc.symm
 have hold13 := UniformClosedRule13.NativeProof.exactNativeRefinement old hold
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have hfa : evaluate (HistoryRuleSuffix.applyTwo LiteralSyntaxValidator.formulaValidator (HistoryRuleSuffix.constant 1 1) termCode) v =
  HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula 1 a) := by
  rw [twoEval,constantEval,← ha,LiteralSyntaxValidator.NativeProof.formulaEncoded]
 have htb : evaluate (HistoryRuleSuffix.applyOne termValidator RawAddSucc.secondTermCode) v =
  HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 b) := by
  rw [oneEval,← hb,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 have htc : evaluate (HistoryRuleSuffix.applyOne termValidator thirdTermCode) v =
  HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 c) := by
  rw [oneEval,← hc,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 simp only [logicalLeaf,chooseEval,recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,
  hl,equalEval,hfa,htb,htc,constantEval,List.Vector.get_zero]
 by_cases he : v.head = Encodable.encode (nativeLine a b c)
 · by_cases hva : GorbowSyntaxValidation.validFormula 1 a = true
   · by_cases hvb : GorbowSyntaxValidation.validTerm 0 b = true
     · by_cases hvc : GorbowSyntaxValidation.validTerm 0 c = true
       · have hf : HistoryDispatcher.logicalFunction v = 1 := by
          rw [hv,he]; exact rawLineAccepted a b c hva hvb hvc
         simp [he,hva,hvb,hvc,HistoryDispatcher.truth,hf]
       · simp [he,hva,hvb,hvc,HistoryDispatcher.truth,hold13]
     · simp [he,hva,hvb,HistoryDispatcher.truth,hold13]
   · simp [he,hva,HistoryDispatcher.truth,hold13]
 · simp [he,hold13]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.NativeProof
