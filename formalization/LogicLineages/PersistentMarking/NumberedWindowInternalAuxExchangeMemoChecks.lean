module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalRawListRecursion (lookup)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorTwo vectorThree)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (rowAuxPair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalAuxExchangeMemoTargets
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

private theorem fieldsSound {n d c f a : Nat} (found : auxFields n = some (d,c,f,a)) :
    n = auxRaw d c f a := by
  unfold auxFields at found
  split at found
  next dom cod fn arg reported =>
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    rcases found with ⟨rfl,rfl,rfl,rfl⟩
    exact codeOfNode reported
  next => cases found

private theorem childSound {a b f g : Nat} (found : guardedAuxChildren a b = some (f,g)) :
    ∃ dom cod arg, a = auxRaw dom cod f arg ∧ b = auxRaw dom cod g arg ∧
      (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true := by
  cases left : auxFields a with
  | none => simp [guardedAuxChildren,left] at found
  | some ab =>
    rcases ab with ⟨dom,cod,fn,arg⟩
    cases right : auxFields b with
    | none => simp [guardedAuxChildren,left,right] at found
    | some bb =>
      rcases bb with ⟨dom',cod',fn',arg'⟩
      have chosen : (if dom = dom' ∧ cod = cod' ∧ arg = arg' ∧
          (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true then some (fn,fn') else none) =
          some (f,g) := by simpa only [guardedAuxChildren,left,right,Option.bind_eq_bind,Option.bind_some] using found
      split at chosen
      next valid =>
        obtain ⟨rfl,rfl,rfl,validA,validB⟩ := valid
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj chosen)
        exact ⟨dom,cod,arg,fieldsSound left,fieldsSound right,validA,validB⟩
      next => cases chosen

private theorem preserve {hp : HeadPairs} {a b f g : Nat} (view : guardedAuxChildren a b = some (f,g))
    (move : (bits hp f g).1 = true) : (bits hp a b).1 = true := by
  obtain ⟨dom,cod,arg,rfl,rfl,validA,validB⟩ := childSound view
  simp only [bits,Bool.and_eq_true,and_assoc] at move
  have lifted : (row hp (auxRaw dom cod f arg) (auxRaw dom cod g arg)).1 = true := by
    rw [rowAuxPair]
    simp [move.2.2]
  simp [bits,validA,validB,lifted]

private def reference (hp : HeadPairs) (key : Nat) : Nat :=
  ((decode key).map (fun p => (bits hp p.1 p.2).1.toNat)).getD 0

private theorem referencePair (hp : HeadPairs) (f g : Nat) :
    reference hp (pair f g) = (bits hp f g).1.toNat := by
  simp [reference,encodedPair]

private theorem baseValue (s : Settings) (base : Program 2) (cal : ActualTermExchange s base) (a b : Nat) :
    evaluate base (a ::ᵥ b ::ᵥ nil) = (bits s.equivalentHeads a b).1.toNat := by
  have row := cal a b
  rw [vectorTwo] at row
  exact row

private theorem stepPreserves (s : Settings) (base : Program 2) (cal : ActualTermExchange s base)
    (i old : Nat) (earlier : ∀ child, child < i+1 →
      evaluate lookup ((i-child) ::ᵥ old ::ᵥ nil) = reference s.equivalentHeads child) :
    stepValue base i old = reference s.equivalentHeads (i+1) := by
  cases paired : decode (i+1) with
  | none => simp [stepValue,reference,paired]
  | some p =>
    rcases p with ⟨a,b⟩
    cases picked : guardedAuxChildren a b with
    | none => simpa [stepValue,reference,paired,picked] using baseValue s base cal a b
    | some q =>
      rcases q with ⟨f,g⟩
      by_cases active : pair f g < i+1 ∧ evaluate lookup ((i-pair f g) ::ᵥ old ::ᵥ nil) = 1
      · have childOne := active.2
        rw [earlier _ active.1,referencePair] at childOne
        have move : (bits s.equivalentHeads f g).1 = true := by
          cases h : (bits s.equivalentHeads f g).1 <;> simp [h] at childOne ⊢
        simp [stepValue,reference,paired,picked,active,preserve picked move]
      · simpa [stepValue,reference,paired,picked,active] using baseValue s base cal a b

private theorem values (s : Settings) (base : Program 2) (R : Program 4)
    (cal : ActualTermExchange s base) (step : StepCalibrated base R) (key : Nat) :
    evaluate (scratchRow (constantZero 2) R) (key ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = reference s.equivalentHeads key := by
  induction key using Nat.strongRecOn with
  | ind key ih =>
    cases key with
    | zero =>
      rw [rowZero]
      change 0 = reference s.equivalentHeads (pair 0 0)
      rw [referencePair]
      rfl
    | succ i =>
      rw [rowSucc,step]
      apply stepPreserves s base cal
      intro child below
      rw [lookupAt (constantZero 2) R (0 ::ᵥ 0 ::ᵥ nil) i child (Nat.le_of_lt_succ below)]
      exact ih child below

theorem exact_AuxExchangeMemoCalibration : ExactAuxExchangeMemoCalibration := by
  intro s base R cal step a b
  rw [vectorTwo]
  change evaluate (selected R) (a ::ᵥ b ::ᵥ nil) = _
  let xs := a ::ᵥ b ::ᵥ nil
  let parts : Fin 3 → Program 2 := ![NumberedWindowInternalSparsePair.pair,constantZero 2,constantZero 2]
  change evaluate (scratchRow (constantZero 2) R) (List.Vector.ofFn (fun i => evaluate (parts i) xs)) = _
  rw [vectorThree]
  change evaluate (scratchRow (constantZero 2) R)
    (evaluate NumberedWindowInternalSparsePair.pair xs ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = _
  rw [NumberedWindowInternalSparsePairEvaluationProof.pairValue,values s base R cal step,referencePair]

#print axioms exact_AuxExchangeMemoCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoChecks
