module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.NativeProof
open GorbowPRProgram GorbowSyntax List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)

theorem termTasksEval (code : Nat) : evaluate termTasks (code ::ᵥ nil) =
 Encodable.encode [((0,0) : GorbowSyntaxValidation.Task)] := by
 simp only [termTasks,twoEval,constantEval,HistoryCodec.NativeProof.nativePair,
  HistoryCodec.NativeProof.nativeConsAllVectors]
 rfl

theorem nativeTerm : Targets.NativeTerm := by
 intro raw
 simp only [termValidator,twoEval,termScan,termTasksEval,projectionEval,List.Vector.get_cons_zero,constantEval]
 rw [LiteralSyntaxScan.NativeProof.scanEncoded,equalEval]
 have he : (Encodable.encode (GorbowSyntaxValidation.scan [(0,0)] raw) = 1) ↔
   GorbowSyntaxValidation.scan [(0,0)] raw = some [] := by
  change (Encodable.encode (GorbowSyntaxValidation.scan [(0,0)] raw) =
   Encodable.encode (some ([] : List GorbowSyntaxValidation.Task))) ↔ _
  exact Encodable.encode_injective.eq_iff
 by_cases h : GorbowSyntaxValidation.scan [(0,0)] raw = some []
 · simp [he,GorbowSyntaxValidation.validTerm,HistoryDispatcher.truth,h]
 · simp [he,GorbowSyntaxValidation.validTerm,HistoryDispatcher.truth,h]

theorem leftEval (q : Program 1) (v : List.Vector Nat 1) :
 evaluate (left q) v = (Nat.unpair (evaluate q v)).1 := by
 rw [left,oneEval,HistoryDecoder.NativeProof.evaluateDecoder]

theorem rightEval (q : Program 1) (v : List.Vector Nat 1) :
 evaluate (right q) v = (Nat.unpair (evaluate q v)).2 := by
 rw [right,oneEval,HistoryDecoder.NativeProof.evaluateDecoder]

def rawLine (raw : List Nat) : GorbowProofChecker.Line := (0,0::(raw++raw),0,11,[raw],0,0)

theorem reflexiveLineEval (term : Program 1) (v : List.Vector Nat 1) (raw : List Nat)
 (ht : evaluate term v = Encodable.encode raw) :
 evaluate (reflexiveLine term) v = Encodable.encode (rawLine raw) := by
 have hp (a b : Nat) : evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) = Nat.pair a b :=
  HistoryCodec.NativeProof.nativePair _
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 simp only [reflexiveLine,reflexiveRaw,twoEval,constantEval,ht,
  appendList,hp,hc]
 rfl

theorem rawLineAccepted (raw : List Nat) (ht : GorbowSyntaxValidation.validTerm 0 raw = true) :
 HistoryDispatcher.logicalFunction (Encodable.encode (rawLine raw) ::ᵥ nil) = 1 := by
 have hc : GorbowLogicalAxiomCode.compile 0 (11,[raw]) = some (0::(raw++raw)) := by
  simp [GorbowLogicalAxiomCode.compile,GorbowLogicalAxiomCode.case11,
   GorbowLogicalAxiomCode.guardTerms,GorbowLogicalAxiomCode.arg,
   GorbowCodeConstructors.binary,ht]
 simp [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,rawLine,HistoryDispatcher.truth,hc]

theorem nativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 obtain ⟨raw,hr⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal
  (evaluate termCode v)
 have hl := reflexiveLineEval termCode v raw hr.symm
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have ht : evaluate (HistoryRuleSuffix.applyOne termValidator termCode) v =
  HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 raw) := by
  rw [oneEval,← hr,nativeTerm]
 simp only [logicalLeaf,chooseEval,recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,
  hl,equalEval,ht,constantEval,List.Vector.get_zero]
 by_cases he : v.head = Encodable.encode (rawLine raw)
 · by_cases hvalid : GorbowSyntaxValidation.validTerm 0 raw = true
   · have h := rawLineAccepted raw hvalid
     have hf : HistoryDispatcher.logicalFunction v = 1 := by
      rw [hv,he]; exact h
     simp [he,hvalid,HistoryDispatcher.truth,hf]
   · simp [he,hvalid,HistoryDispatcher.truth,hold]
 · simp [he,hold]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.NativeProof
