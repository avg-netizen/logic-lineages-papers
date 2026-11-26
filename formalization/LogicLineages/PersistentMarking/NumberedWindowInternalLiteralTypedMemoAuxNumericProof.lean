module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserverFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoAuxNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open GorbowVerifierNormalization (normalize)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalSparseScalarEdge (packedEdge)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne compositeTwo compareEvaluation)
open NumberedWindowInternalLiteralEdgeObserverFitProof (WholeEdgeFit)
open NumberedWindowInternalLiteralTypedAuxExchangeCasesProof (exact_LiteralTypedAuxExchangeCases)

open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionOne)

abbrev memoGuardTape (ctx ty a b : Nat) : List.Vector Nat 4 := ctx ::ᵥ ty ::ᵥ a ::ᵥ b ::ᵥ nil

private theorem selectedValue (p : Program 1) (i : Fin 4) (xs : List.Vector Nat 4) :
    evaluate (readSlot p i) xs = run p (xs.get i) := by
  rw [readSlot,compositeOne]
  rfl

private theorem fieldOn {ctx ty a b d c f r d' c' f' r' : Nat}
    (ha : unpackNode a = some (6,[d,c,f,r])) (hb : unpackNode b = some (6,[d',c',f',r'])) :
    let xs := memoGuardTape ctx ty a b
    (evaluate (fieldSlot 2 0) xs = d ∧ evaluate (fieldSlot 2 1) xs = c ∧
      evaluate (fieldSlot 2 2) xs = f ∧ evaluate (fieldSlot 2 3) xs = r) ∧
    (evaluate (fieldSlot 3 0) xs = d' ∧ evaluate (fieldSlot 3 1) xs = c' ∧
      evaluate (fieldSlot 3 2) xs = f' ∧ evaluate (fieldSlot 3 3) xs = r') := by
  dsimp only
  simp only [selectedValue]
  change (run (field 0) a = d ∧ run (field 1) a = c ∧ run (field 2) a = f ∧ run (field 3) a = r) ∧
    (run (field 0) b = d' ∧ run (field 1) b = c' ∧ run (field 2) b = f' ∧ run (field 3) b = r')
  exact ⟨termFields ha,termFields hb⟩

private theorem fourValue (p : Program 4) (inputs : Fin 4 → Program 4) (xs : List.Vector Nat 4) :
    evaluate (.composition p inputs) xs = evaluate p
      (evaluate (inputs 0) xs ::ᵥ evaluate (inputs 1) xs ::ᵥ evaluate (inputs 2) xs ::ᵥ evaluate (inputs 3) xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn _) = _
  rw [vectorFour]

private theorem calculate (E : Program 4) (ctx ty a b d c f u f' u' : Nat)
    (ha : unpackNode a = some (6,[d,c,f,u])) (hb : unpackNode b = some (6,[d,c,f',u']))
    (fit : (evaluate E (memoGuardTape ctx (arrow d c) f f') = 1 ∧ u = u') ∨
      (f = f' ∧ evaluate E (memoGuardTape ctx d u u') = 1)) :
    evaluate (validateAuxiliary E) (memoGuardTape ctx ty a b) = 1 := by
  let xs := memoGuardTape ctx ty a b
  obtain ⟨l,r⟩ := fieldOn (ctx := ctx) (ty := ty) ha hb
  have equals (j x y : Nat) (aRep : evaluate (fieldSlot 2 j) xs = x) (bRep : evaluate (fieldSlot 3 j) xs = y) :
      evaluate (sameField j) xs = if x = y then 1 else 0 := by
    rw [sameField,compositeTwo,aRep,bRep]
    exact compareEvaluation x y
  have type : evaluate functionType xs = arrow d c := by
    rw [functionType,consOf,compositeTwo,l.1,l.2.1,consValue]
    rfl
  have fn : evaluate (functionChildEdge E) xs = evaluate E (memoGuardTape ctx (arrow d c) f f') := by
    rw [functionChildEdge,fourValue]
    change evaluate E (ctx ::ᵥ evaluate functionType xs ::ᵥ evaluate (fieldSlot 2 2) xs ::ᵥ
      evaluate (fieldSlot 3 2) xs ::ᵥ nil) = _
    rw [type,l.2.2.1,r.2.2.1]
  have arg : evaluate (argumentChildEdge E) xs = evaluate E (memoGuardTape ctx d u u') := by
    rw [argumentChildEdge,fourValue]
    change evaluate E (ctx ::ᵥ evaluate (fieldSlot 2 0) xs ::ᵥ evaluate (fieldSlot 2 3) xs ::ᵥ
      evaluate (fieldSlot 3 3) xs ::ᵥ nil) = _
    rw [l.1,l.2.2.2,r.2.2.2]
  have active : evaluate (readSlot termShape 3) xs = 1 := by
    rw [selectedValue]
    exact (termOne b).mpr ⟨d,c,f',u',hb⟩
  have ch : evaluate (chooseChild E) xs = 1 := by
    rw [chooseChild,evalBranch,GorbowVerifierNormalization.Proof.actualEvaluation.2]
    rcases fit with left | right
    · have this : evaluate (functionCase E) xs = 1 := by
        rw [functionCase,actualConjunctionEvaluation,fn,equals 3 u u' l.2.2.2 r.2.2.2,left.1,if_pos left.2]
        rfl
      rw [this]
      rfl
    · have this : evaluate (argumentCase E) xs = 1 := by
        rw [argumentCase,actualConjunctionEvaluation,arg,equals 2 f f' l.2.2.1 r.2.2.1,right.2,if_pos right.1]
        rfl
      split
      · rfl
      · exact this
  change evaluate (validateAuxiliary E) xs = _
  rw [validateAuxiliary,actualConjunctionEvaluation,actualConjunctionEvaluation,actualConjunctionEvaluation,
    active,equals 0 d d l.1 r.1,equals 1 c c l.2.1 r.2.1,ch]
  simp

/-- Numeric completeness of the single physical stage when its actual
child callback accepts one of the two typed alternatives. -/
theorem exact_LiteralAuxiliaryTypedStageAccept (E : Program 4) (ctx ty a b d c f u f' u' : Nat)
    (ha : unpackNode a = some (6,[d,c,f,u])) (hb : unpackNode b = some (6,[d,c,f',u']))
    (calls : (evaluate E (memoGuardTape ctx (arrow d c) f f') = 1 ∧ u = u') ∨
      (f = f' ∧ evaluate E (memoGuardTape ctx d u u') = 1)) :
    evaluate (typedAuxEdgeGuard (constantOne 4) E) (memoGuardTape ctx ty a b) = 1 := by
  have shape : run termShape ((memoGuardTape ctx ty a b).get 2) = 1 := (termOne a).mpr ⟨d,c,f,u,ha⟩
  rw [typedAuxEdgeGuard,conjunctionOne]
  refine ⟨rfl,?_⟩
  rw [auxChildGuard,evalBranch,selectedValue,shape,if_neg (by decide)]
  exact calculate E ctx ty a b d c f u f' u' ha hb calls

theorem exact_LiteralNonAuxiliaryTypedStageAccept (E : Program 4) (ctx ty a b : Nat)
    (zero : run termShape a = 0) :
    evaluate (typedAuxEdgeGuard (constantOne 4) E) (memoGuardTape ctx ty a b) = 1 := by
  have shape : run termShape ((memoGuardTape ctx ty a b).get 2) = 0 := zero
  rw [typedAuxEdgeGuard,conjunctionOne]
  refine ⟨rfl,?_⟩
  rw [auxChildGuard,evalBranch,selectedValue,shape,if_pos rfl]
  rfl

#print axioms exact_LiteralAuxiliaryTypedStageAccept
#print axioms exact_LiteralNonAuxiliaryTypedStageAccept
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoAuxNumericProof
