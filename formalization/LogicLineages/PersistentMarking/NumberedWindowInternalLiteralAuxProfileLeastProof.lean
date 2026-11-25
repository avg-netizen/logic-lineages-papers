module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastAuxPhysicalProfileProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalLessThan (constantOne)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration packedLeast encodeState)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne compositeTwo predEvaluation compareEvaluation)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (pairFirst pairSecond outRaw)
open NumberedWindowInternalLiteralLeastAuxPhysicalProfileProof
  (physicalAuxProfile exact_LiteralPackedLeastPhysicalAuxProfile)
open NumberedWindowScalarAlgorithm (Settings)

def functionHead : Program 1 := .composition cellHead (Fin.cons (field 2) Fin.elim0)
def decodedOutput (p : Program 1) : Program 2 := .composition p (Fin.cons outRaw Fin.elim0)
def matchCoordinates (p : Program 1) : Program 2 :=
  .composition compareNumbers (Fin.cons (pairFirst p) (Fin.cons (decodedOutput p) Fin.elim0))

def fieldMatch : Program 2 :=
  conjunction (matchCoordinates (field 0))
    (conjunction (matchCoordinates (field 1)) (matchCoordinates functionHead))

def auxFieldsIfPresent : Program 2 := branch (pairFirst termShape) (constantOne 2) fieldMatch

def auxProfileTest : Program 2 := conjunction (matchCoordinates termShape) auxFieldsIfPresent

def retainAuxProfile : Program 2 := branch auxProfileTest (constantZero 2) (.projection 1)

/-- In addition to the top-header and atomic checks, the physical
least output can retain the auxiliary arity, arrow coordinates, and
leading raw function constructor. On non-auxiliary inputs it only
checks agreement of the auxiliary shape bit. -/
def auxProfileLeast (L : Program 3) : Program 3 :=
  .composition retainAuxProfile (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))

theorem functionHeadValue (q : Nat) : run functionHead q = run cellHead (run (field 2) q) := by
  unfold run functionHead
  rw [compositeOne]

private theorem firstValue (p : Program 1) (q k : Nat) :
    evaluate (pairFirst p) (q ::ᵥ k ::ᵥ nil) = run p q := by
  rw [pairFirst,compositeOne]
  rfl

private theorem outputValue (p : Program 1) (q k : Nat) :
    evaluate (decodedOutput p) (q ::ᵥ k ::ᵥ nil) = run p k.pred := by
  rw [decodedOutput,compositeOne,outRaw,pairSecond,compositeOne]
  have select : evaluate (.projection (1 : Fin 2)) (q ::ᵥ k ::ᵥ nil) = k := rfl
  rw [select,predEvaluation]
  rfl

theorem coordinateValue (p : Program 1) (q k : Nat) :
    evaluate (matchCoordinates p) (q ::ᵥ k ::ᵥ nil) =
      if run p q = run p k.pred then 1 else 0 := by
  rw [matchCoordinates,compositeTwo,firstValue,outputValue]
  exact compareEvaluation _ _

private theorem shapeBit (q : Nat) : run termShape q = 0 ∨ run termShape q = 1 := by
  unfold termShape nodeGood run
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem profileTestAccepts (q k : Nat) (same : physicalAuxProfile q = physicalAuxProfile k) :
    evaluate auxProfileTest (q ::ᵥ (k+1) ::ᵥ nil) = 1 := by
  let xs := q ::ᵥ (k+1) ::ᵥ nil
  have coords : ∀ p, evaluate (matchCoordinates p) xs = if run p q = run p k then 1 else 0 := by
    intro p
    exact coordinateValue p q (k+1)
  have finish (shape : run termShape q = run termShape k)
      (fields : evaluate auxFieldsIfPresent xs = 1) : evaluate auxProfileTest xs = 1 := by
    rw [auxProfileTest,actualConjunctionEvaluation,coords,if_pos shape,fields]
    rfl
  rcases shapeBit q with no | yes
  · have right : run termShape k = 0 := by
      rcases shapeBit k with h | h
      · exact h
      · simp [physicalAuxProfile,no,h] at same
    apply finish (no.trans right.symm)
    rw [auxFieldsIfPresent,evalBranch,firstValue,no]
    rfl
  · have right : run termShape k = 1 := by
      rcases shapeBit k with h | h
      · simp [physicalAuxProfile,yes,h] at same
      · exact h
    have eqs : run (field 0) q = run (field 0) k ∧
        run (field 1) q = run (field 1) k ∧ run functionHead q = run functionHead k := by
      simp only [physicalAuxProfile,yes,right,if_pos,Option.some.injEq,Prod.mk.injEq] at same
      simpa only [functionHeadValue] using same
    apply finish (yes.trans right.symm)
    rw [auxFieldsIfPresent,evalBranch,firstValue,yes]
    change evaluate fieldMatch xs = 1
    rw [fieldMatch,actualConjunctionEvaluation,actualConjunctionEvaluation,
      coords,coords,coords,if_pos eqs.1,if_pos eqs.2.1,if_pos eqs.2.2]
    rfl

/-- Retaining the computed auxiliary profile changes no numerical
answer, on either branch and for every raw input to the original least. -/
theorem exact_LiteralAuxProfileLeast (s : Settings) (L : Program 3)
    (cal : ActualLeastCalibration s L) : ActualLeastCalibration s (auxProfileLeast L) := by
  intro ctx ty q
  rw [auxProfileLeast,compositeTwo,cal ctx ty q]
  change evaluate retainAuxProfile (q ::ᵥ encodeState (packedLeast s ctx ty q) ::ᵥ nil) = _
  cases got : packedLeast s ctx ty q with
  | none =>
    change evaluate retainAuxProfile (q ::ᵥ 0 ::ᵥ nil) = 0
    rw [retainAuxProfile,evalBranch]
    split <;> rfl
  | some k =>
    change evaluate retainAuxProfile (q ::ᵥ (k+1) ::ᵥ nil) = k+1
    have test := profileTestAccepts q k (exact_LiteralPackedLeastPhysicalAuxProfile s ctx ty q k got)
    rw [retainAuxProfile,evalBranch,test]
    rfl

#print axioms exact_LiteralAuxProfileLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastProof
