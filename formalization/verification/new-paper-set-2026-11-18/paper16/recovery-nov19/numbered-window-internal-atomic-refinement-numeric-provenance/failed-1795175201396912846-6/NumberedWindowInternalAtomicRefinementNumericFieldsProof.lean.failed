module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalAtomicRefinement NumberedWindowInternalAtomicRefinementNumericTargets
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeTwo vectorOne literalEvaluation zeroEvaluation compareEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAtomicRawStep (bottomRaw)
open NumberedWindowAtomicPositiveTargets (packedAddress bottomAddress)

theorem literalFields (c t k : Nat) :
    run rawContext (packedAddress c t k) = c ∧
    run rawResult (packedAddress c t k) = t ∧
    run rawLeast (packedAddress c t k) = k := by
  let q := pair 3 (pack [c,t,k])+1
  have outer : run cellTail q = pack [c,t,k] :=
    (headTailOfCell (cellAt 3 (pack [c,t,k]))).2
  have first : run cellHead (pack [c,t,k]) = c ∧ run cellTail (pack [c,t,k]) = pack [t,k] :=
    headTailOfCell (cellAt c (pack [t,k]))
  have second : run cellHead (pack [t,k]) = t ∧ run cellTail (pack [t,k]) = pack [k] :=
    headTailOfCell (cellAt t (pack [k]))
  have third : run cellHead (pack [k]) = k :=
    (headTailOfCell (cellAt k (pack []))).1
  change run rawContext q = c ∧ run rawResult q = t ∧ run rawLeast q = k
  exact ⟨by simp only [rawContext,field,cursor,applyValue,outer,first.1],
    by simp only [rawResult,field,cursor,applyValue,outer,first.2,second.1],
    by simp only [rawLeast,field,cursor,applyValue,outer,first.2,second.2,third]⟩

theorem firstField (tag t : Nat) (fs : List Nat) :
    run (field 0) (packNode tag (t::fs)) = t := by
  let q := pair tag (pack (t::fs))+1
  have outer : run cellTail q = pack (t::fs) :=
    (headTailOfCell (cellAt tag (pack (t::fs)))).2
  have head : run cellHead (pack (t::fs)) = t :=
    (headTailOfCell (cellAt t (pack fs))).1
  change run (field 0) q = t
  simp only [field,cursor,applyValue,outer,head]

theorem sourceValue (p : Program 1) (x w y : Nat) :
    evaluate (atSource p) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = run p x := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (.projection (0 : Fin 3)) (x ::ᵥ w ::ᵥ y ::ᵥ nil)) = _
  rw [vectorOne] <;> rfl

theorem targetValue (p : Program 1) (x w y : Nat) :
    evaluate (atTarget p) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = run p y := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (.projection (2 : Fin 3)) (x ::ᵥ w ::ᵥ y ::ᵥ nil)) = _
  rw [vectorOne] <;> rfl

private theorem consValue {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (consOf p q) xs = pair (evaluate p xs) (evaluate q xs) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

theorem emitterValue (c t : Nat) :
    evaluate bottomEmitter (c ::ᵥ t ::ᵥ nil) = bottomAddress c t := by
  let xs := c ::ᵥ t ::ᵥ nil
  have h0 : evaluate (.projection (0 : Fin 2)) xs = c := rfl
  have h1 : evaluate (.projection (1 : Fin 2)) xs = t := rfl
  change evaluate bottomEmitter xs = _
  simp only [bottomEmitter,consValue,h0,h1,zeroEvaluation,literalEvaluation,
    bottomAddress,packedAddress,bottomRaw,packNode,pack]

theorem bottomOfValue (c t k : Nat) :
    run bottomOf (packedAddress c t k) = bottomAddress c t := by
  obtain ⟨hc,ht,_⟩ := literalFields c t k
  unfold run at hc ht ⊢
  rw [bottomOf,compositeTwo,hc,ht,emitterValue]

theorem exactBottomTarget : ExactNumericAtomicBottomTarget := by
  refine ⟨emitterValue,?_⟩
  intro c t k w y
  rw [bottomTarget,compositeTwo,sourceValue,bottomOfValue]
  exact compareEvaluation y (bottomAddress c t)

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
