module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open SixSol20261113.HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)
open TwoSol20261113.ReflexivityRecognizer
open TwoSol20261113.ReflexivityRecognizer.NativeProof

theorem lineEval (term : Program 1) (v : List.Vector Nat 1) (raw : List Nat)
 (ht : evaluate term v = Encodable.encode raw) :
 evaluate (line term) v = Encodable.encode (RawAddZero.nativeLine raw) := by
 have hp (a b : Nat) : evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) = Nat.pair a b :=
  HistoryCodec.NativeProof.nativePair _
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 have hz : evaluate zeroRaw v = Encodable.encode ([1] : List Nat) := by
  simp only [zeroRaw,twoEval,constantEval,hc]
  rfl
 have ha : evaluate (addZeroRaw term) v = Encodable.encode (3 :: (raw ++ [1])) := by
  simp only [addZeroRaw,twoEval,constantEval,ht,hz,appendList,hc]
  rfl
 have he : evaluate (equalityRaw term) v = Encodable.encode (0 :: ((3 :: (raw ++ [1])) ++ raw)) := by
  simp only [equalityRaw,twoEval,constantEval,ha,ht,appendList,hc]
  rfl
 simp only [line,twoEval,constantEval,ht,he,hp,hc]
 rfl

theorem nativeLine : Targets.NativeLine := by
 intro raw
 exact lineEval (.projection 0) (Encodable.encode raw ::ᵥ nil) raw rfl

theorem rawLineAccepted (raw : List Nat) (ht : GorbowSyntaxValidation.validTerm 0 raw = true) :
 HistoryDispatcher.arithmeticFunction (Encodable.encode (RawAddZero.nativeLine raw) ::ᵥ nil) = 1 := by
 have hc : GorbowArithmeticAxiomCode.compile 0 (2,[raw]) =
  some (GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.binary 3 raw [1]) raw) := by
  simp [GorbowArithmeticAxiomCode.compile,GorbowArithmeticAxiomCode.case2,
   GorbowLogicalAxiomCode.guardTerms,GorbowLogicalAxiomCode.arg,ht]
 simp [HistoryDispatcher.arithmeticFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,RawAddZero.nativeLine,HistoryDispatcher.truth,hc]

theorem nativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 obtain ⟨raw,hr⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal
  (evaluate termCode v)
 have hl := lineEval termCode v raw hr.symm
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have ht : evaluate (applyOne termValidator termCode) v =
  HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 raw) := by
  rw [oneEval,← hr,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 simp only [arithmeticLeaf,chooseEval,recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,
  hl,equalEval,ht,constantEval,List.Vector.get_zero]
 by_cases he : v.head = Encodable.encode (RawAddZero.nativeLine raw)
 · by_cases hvalid : GorbowSyntaxValidation.validTerm 0 raw = true
   · have h := rawLineAccepted raw hvalid
     have hf : HistoryDispatcher.arithmeticFunction v = 1 := by
      rw [hv,he]; exact h
     simp [he,hvalid,HistoryDispatcher.truth,hf]
   · simp [he,hvalid,HistoryDispatcher.truth,hold]
 · simp [he,hold]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.NativeProof.nativeLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.NativeProof.nativeRefinement
