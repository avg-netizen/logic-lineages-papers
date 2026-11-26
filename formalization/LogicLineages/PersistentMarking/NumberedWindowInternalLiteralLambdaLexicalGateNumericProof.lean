module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaBodyWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode pack packNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail cellGood)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell flagOfCell)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo vectorThree)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow packedWindow)
open NumberedWindowInternalLiteralLambdaLexicalGateProof
open NumberedWindowInternalLiteralLambdaBodyWindowNumericProof (exact_LiteralOriginalLambdaBothBodyWindows)

abbrev typedTape (c t q w r : Nat) := c ::ᵥ t ::ᵥ q ::ᵥ w ::ᵥ r ::ᵥ nil

theorem evalLexicalSlot (p : Program 1) (i : Fin 5) (v : List.Vector Nat 5) :
    evaluate (lexicalSlot p i) v = run p (v.get i) := by
  unfold lexicalSlot run
  rw [evaluate,vectorOne]
  rfl

theorem evalLiteralLambdaFields (q d b : Nat) (h : unpackNode q = some (2,[d,b])) :
    run (field 0) q = d ∧ run (field 1) q = b := by
  rw [codeOfNode h]
  have outer := (headTailOfCell (cellAt 2 (pack [d,b]))).2
  have first : run cellHead (pack [d,b]) = d ∧ run cellTail (pack [d,b]) = pack [b] :=
    headTailOfCell (cellAt d (pack [b]))
  have last : run cellHead (pack [b]) = b := (headTailOfCell (cellAt b (pack []))).1
  change run (field 0) (pair 2 (pack [d,b]) + 1) = d ∧ _
  simp only [field,cursor,applyValue,packNode,outer,first.1,first.2,last,and_self]

theorem evalConsOf {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (consOf p q) v = pair (evaluate p v) (evaluate q v) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

theorem evalBinaryComposition {n : Nat} (p : Program 2) (a b : Program n) (v : List.Vector Nat n) :
    evaluate (.composition p (![a,b] : Fin 2 → Program n)) v =
      evaluate p (evaluate a v ::ᵥ evaluate b v ::ᵥ nil) := by
  rw [evaluate,vectorTwo]
  rfl

theorem evalTernaryComposition {n : Nat} (p : Program 3) (a b c : Program n) (v : List.Vector Nat n) :
    evaluate (.composition p (![a,b,c] : Fin 3 → Program n)) v =
      evaluate p (evaluate a v ::ᵥ evaluate b v ::ᵥ evaluate c v ::ᵥ nil) := by
  rw [evaluate,vectorThree]
  rfl

theorem exact_LiteralLexicalGateEvaluates (W : Program 3) (s : Settings) (fit : ActualPackedWindow s W)
    (c t q w r d a b cod : Nat)
    (source : unpackNode q = some (2,[d,a])) (dest : unpackNode r = some (2,[d,b]))
    (type : t = arrow d cod)
    (left : packedWindow s (pair d c + 1) cod a = true)
    (right : packedWindow s (pair d c + 1) cod b = true) :
    evaluate (lambdaLexicalGate W) (typedTape c t q w r) = 1 := by
  subst t
  let v := typedTape c (arrow d cod) q w r
  obtain ⟨d₀,a₀⟩ := evalLiteralLambdaFields q d a source
  obtain ⟨_,b₀⟩ := evalLiteralLambdaFields r d b dest
  obtain ⟨readHead,readTail⟩ := headTailOfCell (cellAt d cod)
  have validity := flagOfCell (cellAt d cod)
  have binder : evaluate lexicalBinder v = d := by rw [lexicalBinder,evalLexicalSlot]; exact d₀
  have domain : evaluate lexicalDomain v = d := by rw [lexicalDomain,evalLexicalSlot]; exact readHead
  have codomain : evaluate lexicalCodomain v = cod := by rw [lexicalCodomain,evalLexicalSlot]; exact readTail
  have before : evaluate lexicalSourceBody v = a := by rw [lexicalSourceBody,evalLexicalSlot]; exact a₀
  have after : evaluate lexicalTargetBody v = b := by rw [lexicalTargetBody,evalLexicalSlot]; exact b₀
  have scope : evaluate lexicalContext v = pair d c + 1 := by rw [lexicalContext,evalConsOf,binder]; rfl
  simp only [lambdaLexicalGate,lexicalArrow,conjunctionOne]
  change (evaluate (lexicalSlot cellGood 1) v = 1 ∧ _ ) ∧ _ ∧ _
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · rw [evalLexicalSlot]; exact validity
  · rw [evalBinaryComposition,domain,binder,exactEqualityEvaluation,if_pos rfl]
  · rw [lexicalWindowAt,evalTernaryComposition,scope,codomain,before,fit,left]; rfl
  · rw [lexicalWindowAt,evalTernaryComposition,scope,codomain,after,fit,right]; rfl

#print axioms evalLexicalSlot
#print axioms evalLiteralLambdaFields
#print axioms evalConsOf
#print axioms evalBinaryComposition
#print axioms evalTernaryComposition
#print axioms exact_LiteralLexicalGateEvaluates
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
