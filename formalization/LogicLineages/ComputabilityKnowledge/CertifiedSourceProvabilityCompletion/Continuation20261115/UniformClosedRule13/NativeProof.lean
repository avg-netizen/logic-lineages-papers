module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.NativeLineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof NativeLineProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open TwoSol20261113.ReflexivityRecognizer
/-- Acceptance by the ORIGINAL logical checker follows from its actual compile13
and instanceCode guards, not from an assumption about the new recognizer. -/
theorem rawLineAccepted (a b : List Nat)
 (ha : GorbowSyntaxValidation.validFormula 1 a = true)
 (hb : GorbowSyntaxValidation.validTerm 0 b = true) :
 HistoryDispatcher.logicalFunction (Encodable.encode (nativeLine a b) ::ᵥ nil) = 1 := by
 let result := GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.unary 10 a)
  (GorbowSubstitutionCode.subRaw 1 1 0 [b] a)
 have hc : GorbowLogicalAxiomCode.case13 0 [a,b] = some result := by
  simp [GorbowLogicalAxiomCode.case13,GorbowLogicalAxiomCode.arg,GorbowInstanceCode.instanceCode,
   GorbowInstanceCode.variableDictionary,GorbowSubstitutionCode.substituteFormulaCode,
   GorbowLiftedDictionary.dictionaryValid,ha,hb,result]
 have hcompile : GorbowLogicalAxiomCode.compile 0 (13,[a,b]) = some result := by
  simp [GorbowLogicalAxiomCode.compile,hc]
 simp [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,nativeLine,HistoryDispatcher.truth,hc,hcompile]
/-- Original function calibration for EVERY numeric line, retaining the old
fallback verbatim on all unmatched or malformed inputs. -/
theorem exactNativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 obtain ⟨a,ha⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate termCode v)
 obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate RawAddSucc.secondTermCode v)
 have hl := lineAt termCode RawAddSucc.secondTermCode v a b ha.symm hb.symm
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have hfa : evaluate (HistoryRuleSuffix.applyTwo LiteralSyntaxValidator.formulaValidator (HistoryRuleSuffix.constant 1 1) termCode) v =
  HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula 1 a) := by
  rw [twoEval,constantEval,← ha,LiteralSyntaxValidator.NativeProof.formulaEncoded]
 have htb : evaluate (HistoryRuleSuffix.applyOne termValidator RawAddSucc.secondTermCode) v =
  HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 b) := by
  rw [oneEval,← hb,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 simp only [logicalLeaf,chooseEval,recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,
  hl,equalEval,hfa,htb,constantEval,List.Vector.get_zero]
 by_cases he : v.head = Encodable.encode (nativeLine a b)
 · by_cases hva : GorbowSyntaxValidation.validFormula 1 a = true
   · by_cases hvb : GorbowSyntaxValidation.validTerm 0 b = true
     · have hf : HistoryDispatcher.logicalFunction v = 1 := by
        rw [hv,he]; exact rawLineAccepted a b hva hvb
       simp [he,hva,hvb,HistoryDispatcher.truth,hf]
     · simp [he,hva,hvb,HistoryDispatcher.truth,hold]
   · simp [he,hva,HistoryDispatcher.truth,hold]
 · simp [he,hold]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.NativeProof
