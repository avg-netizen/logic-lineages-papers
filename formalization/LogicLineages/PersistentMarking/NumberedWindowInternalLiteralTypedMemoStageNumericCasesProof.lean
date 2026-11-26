module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageNumericCasesProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalLessThan (constantOne)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termFields termOne)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo compareEvaluation)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionOne)
open NumberedWindowInternalLiteralTypedMemoEvaluationProof (tape fourEval slotEval)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof

private theorem sameSelectedField (ctx ty a b j x y : Nat)
    (first : run (field j) a = x) (second : run (field j) b = y) :
    evaluate (sameField j) (tape ctx ty a b) = 1 ↔ x = y := by
  rw [sameField,compositeTwo,slotEval,slotEval]
  change evaluate NumberedWindowInternalFreshProbeDispatchProgram.compareNumbers
    (run (field j) a ::ᵥ run (field j) b ::ᵥ nil) = 1 ↔ _
  rw [first,second,compareEvaluation]
  by_cases h : x = y <;> simp [h]

/-- The numeric stage has no unaccounted positive auxiliary arm:
it returns exactly one physical child call and an unchanged other
field. No premise assumes that those calls already match old answers. -/
theorem exact_LiteralTypedMemoStageNumericCases (E : Program 4)
    (ctx ty a b d c f u : Nat) (src : unpackNode a = some (6,[d,c,f,u]))
    (held : evaluate (typedAuxEdgeGuard (constantOne 4) E) (tape ctx ty a b) = 1) :
    ∃ f' u', unpackNode b = some (6,[d,c,f',u']) ∧
      ((evaluate E (tape ctx (arrow d c) f f') = 1 ∧ u = u') ∨
        (f = f' ∧ evaluate E (tape ctx d u u') = 1)) := by
  let xs := tape ctx ty a b
  have source : evaluate (readSlot termShape 2) xs = 1 := by
    rw [slotEval]
    exact (termOne a).mpr ⟨d,c,f,u,src⟩
  have inner := (conjunctionOne (constantOne 4) (auxChildGuard E) xs).mp held
  have run : evaluate (validateAuxiliary E) xs = 1 := by
    have v := inner.2
    rw [auxChildGuard,evalBranch,source,if_neg (by decide)] at v
    exact v
  rw [validateAuxiliary,conjunctionOne,conjunctionOne,conjunctionOne] at run
  obtain ⟨target,domains,codomains,path⟩ := run
  rw [slotEval] at target
  obtain ⟨d',c',f',u',dst⟩ := (termOne b).mp target
  have left := termFields src
  have right := termFields dst
  have dEq := (sameSelectedField ctx ty a b 0 d d' left.1 right.1).mp domains
  have cEq := (sameSelectedField ctx ty a b 1 c c' left.2.1 right.2.1).mp codomains
  subst d'
  subst c'
  refine ⟨f',u',dst,?_⟩
  rw [chooseChild,evalBranch,GorbowVerifierNormalization.Proof.actualEvaluation.2] at path
  by_cases h : evaluate (functionCase E) xs = 1
  · left
    obtain ⟨aFn,fix⟩ := (conjunctionOne (functionChildEdge E) (sameField 3) xs).mp h
    refine ⟨?_,(sameSelectedField ctx ty a b 3 u u' left.2.2.2 right.2.2.2).mp fix⟩
    rw [functionChildEdge,fourEval] at aFn
    change evaluate E (tape ctx (evaluate functionType xs) (evaluate (fieldSlot 2 2) xs)
      (evaluate (fieldSlot 3 2) xs)) = 1 at aFn
    have atType : evaluate functionType xs = arrow d c := by
      rw [functionType,consOf,compositeTwo,slotEval,slotEval]
      change evaluate NumberedWindowInternalSparsePair.fieldCons
        (run (field 0) a ::ᵥ run (field 1) a ::ᵥ nil) = _
      rw [left.1,left.2.1,consValue]
      rfl
    rw [atType,slotEval,slotEval] at aFn
    rw [show run (field 2) (xs.get 2) = f from left.2.2.1,
      show run (field 2) (xs.get 3) = f' from right.2.2.1] at aFn
    exact aFn
  · right
    have aCase : evaluate (argumentCase E) xs = 1 := by simp only [h,if_false,if_pos] at path; exact path
    obtain ⟨fix,aArg⟩ := (conjunctionOne (sameField 2) (argumentChildEdge E) xs).mp aCase
    refine ⟨(sameSelectedField ctx ty a b 2 f f' left.2.2.1 right.2.2.1).mp fix,?_⟩
    rw [argumentChildEdge,fourEval] at aArg
    change evaluate E (tape ctx (evaluate (fieldSlot 2 0) xs) (evaluate (fieldSlot 2 3) xs)
      (evaluate (fieldSlot 3 3) xs)) = 1 at aArg
    rw [slotEval,slotEval,slotEval] at aArg
    rw [show run (field 0) (xs.get 2) = d from left.1,
      show run (field 3) (xs.get 2) = u from left.2.2.2,
      show run (field 3) (xs.get 3) = u' from right.2.2.2] at aArg
    exact aArg

#print axioms exact_LiteralTypedMemoStageNumericCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageNumericCasesProof
