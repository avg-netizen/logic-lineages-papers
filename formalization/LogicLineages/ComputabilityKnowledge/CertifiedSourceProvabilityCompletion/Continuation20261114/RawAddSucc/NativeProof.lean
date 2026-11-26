module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open SixSol20261113.HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)
open TwoSol20261113.ReflexivityRecognizer
open TwoSol20261113.ReflexivityRecognizer.NativeProof
theorem lineEval {n : Nat} (left right : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate left v = Encodable.encode a) (hb : evaluate right v = Encodable.encode b) :
 evaluate (line left right) v = Encodable.encode (RawAddSucc.nativeLine a b) := by
 have hp (a b : Nat) : evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) = Nat.pair a b :=
  HistoryCodec.NativeProof.nativePair _
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 have hs : evaluate (successorRaw right) v = Encodable.encode (2 :: b) := by
  simp only [successorRaw,twoEval,constantEval,hb,hc]; rfl
 have hab : evaluate (additionRaw left right) v = Encodable.encode (3 :: (a ++ b)) := by
  simp only [additionRaw,twoEval,constantEval,ha,hb,appendList,hc]; rfl
 have hleft : evaluate (additionRaw left (successorRaw right)) v = Encodable.encode (3 :: (a ++ (2 :: b))) := by
  simp only [additionRaw,twoEval,constantEval,ha,hs,appendList,hc]; rfl
 have hright : evaluate (successorRaw (additionRaw left right)) v = Encodable.encode (2 :: 3 :: (a ++ b)) := by
  simp only [successorRaw,twoEval,constantEval,hab,hc]; rfl
 have he : evaluate (equalityRaw left right) v = Encodable.encode (0 :: ((3 :: (a ++ (2 :: b))) ++ (2 :: 3 :: (a ++ b)))) := by
  simp only [equalityRaw,twoEval,constantEval,hleft,hright,appendList,hc]; rfl
 simp only [line,twoEval,constantEval,ha,hb,he,hp,hc]
 rfl

theorem nativeLine : Targets.NativeLine := by
 intro a b
 exact lineEval (.projection 0) (.projection 1) (Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ nil) a b rfl rfl

theorem rawLineAccepted (a b : List Nat)
 (ha : GorbowSyntaxValidation.validTerm 0 a = true) (hb : GorbowSyntaxValidation.validTerm 0 b = true) :
 HistoryDispatcher.arithmeticFunction (Encodable.encode (RawAddSucc.nativeLine a b) ::ᵥ nil) = 1 := by
 have hc : GorbowArithmeticAxiomCode.compile 0 (3,[a,b]) =
  some (GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.binary 3 a (GorbowCodeConstructors.unary 2 b))
   (GorbowCodeConstructors.unary 2 (GorbowCodeConstructors.binary 3 a b))) := by
  simp [GorbowArithmeticAxiomCode.compile,GorbowArithmeticAxiomCode.case3,
   GorbowLogicalAxiomCode.guardTerms,GorbowLogicalAxiomCode.arg,ha,hb]
 simp [HistoryDispatcher.arithmeticFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,RawAddSucc.nativeLine,HistoryDispatcher.truth,hc]

theorem nativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 obtain ⟨a,ha⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate termCode v)
 obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate secondTermCode v)
 have hl := lineEval termCode secondTermCode v a b ha.symm hb.symm
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have hta : evaluate (applyOne termValidator termCode) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 a) := by
  rw [oneEval,← ha,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 have htb : evaluate (applyOne termValidator secondTermCode) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 b) := by
  rw [oneEval,← hb,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 simp only [arithmeticLeaf,chooseEval,recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,
  hl,equalEval,hta,htb,constantEval,List.Vector.get_zero]
 by_cases he : v.head = Encodable.encode (RawAddSucc.nativeLine a b)
 · by_cases hva : GorbowSyntaxValidation.validTerm 0 a = true
   · by_cases hvb : GorbowSyntaxValidation.validTerm 0 b = true
     · have hf : HistoryDispatcher.arithmeticFunction v = 1 := by
        rw [hv,he]; exact rawLineAccepted a b hva hvb
       simp [he,hva,hvb,HistoryDispatcher.truth,hf]
     · simp [he,hva,hvb,HistoryDispatcher.truth,hold]
   · simp [he,hva,HistoryDispatcher.truth,hold]
 · simp [he,hold]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.NativeProof.nativeLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc.NativeProof.nativeRefinement
