module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericSlotsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreNumericChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
public import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneOptionApplicationV2

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTest (predecessor)
open InternalEqualityTestEvaluationProof (exactPredecessorEvaluation)
open NumberedWindowAddressApplication (application graph)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowGuardedGraphChecks (exact_GuardEvaluation)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)
open NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof (exactEmitters)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeTwo literalEvaluation vectorOne vectorThree)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawDomain rawCodomain rawLeast)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendNumericChecks (exact_AllInputGuardedApplication)
open NumberedWindowInternalSparseApplicationFrontendNumericSlotsProof (coreAtOne)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseApplicationOutputCore
  (seed selectedLeast selectedClass outputAddress)
open NumberedWindowInternalSparseApplicationOutputCoreNumericChecks (exact_AllInputApplicationOutputCore)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (originalOutput)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration encodeState packedLeast)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowScalarAlgorithm (Settings)

def atInput (p : Program 1) (slot : Fin 2) : Program 2 :=
  .composition p (fun _ => .projection slot)

/-- The original packed output address on the two physical inputs. -/
def candidateAddress (least : Program 3) : Program 2 :=
  .composition (outputAddress least)
    ![atInput rawContext 0, atInput rawDomain 0, atInput rawCodomain 0,
      atInput rawLeast 0, atInput rawLeast 1, constantZero 2]

/-- Emit the optional result precisely when the original application guard
accepts the address emitted from its own least program. -/
def optionApplicationOf (i : Program 1) (least : Program 3) : Program 2 :=
  let candidate := candidateAddress least
  let check := Program.composition (applicationGuard i least) ![.projection 0, .projection 1, candidate]
  branch check (constantZero 2) (.composition .succ (fun _ : Fin 1 => candidate))

private theorem vectorSix (v : Fin 6 → Nat) :
    List.Vector.ofFn v = v 0 ::ᵥ v 1 ::ᵥ v 2 ::ᵥ v 3 ::ᵥ v 4 ::ᵥ v 5 ::ᵥ nil := by
  apply List.Vector.ext
  intro k
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_
    (fun c => Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => ?_) d) c) b) a) k
  · simp <;> rfl
  · simp <;> rfl
  · simp <;> rfl
  · simp <;> rfl
  · simp <;> rfl
  · obtain rfl := Fin.eq_zero e
    simp <;> rfl

private theorem candidateValue (least : Program 3) (f u : Nat) :
    evaluate (candidateAddress least) (f ::ᵥ u ::ᵥ nil) =
      evaluate (outputAddress least) (run rawContext f ::ᵥ run rawDomain f ::ᵥ run rawCodomain f ::ᵥ
        run rawLeast f ::ᵥ run rawLeast u ::ᵥ 0 ::ᵥ nil) := by
  let xs := f ::ᵥ u ::ᵥ nil
  let slots : Fin 6 → Program 2 := ![atInput rawContext 0, atInput rawDomain 0, atInput rawCodomain 0,
    atInput rawLeast 0, atInput rawLeast 1, constantZero 2]
  have left (p : Program 1) : evaluate (atInput p 0) xs = run p f := by
    change evaluate p (List.Vector.ofFn fun _ : Fin 1 => evaluate (.projection (0 : Fin 2)) xs) = _
    rw [vectorOne]
    rfl
  have right (p : Program 1) : evaluate (atInput p 1) xs = run p u := by
    change evaluate p (List.Vector.ofFn fun _ : Fin 1 => evaluate (.projection (1 : Fin 2)) xs) = _
    rw [vectorOne]
    rfl
  change evaluate (outputAddress least) (List.Vector.ofFn fun a : Fin 6 => evaluate (slots a) xs) = _
  rw [vectorSix]
  change evaluate (outputAddress least) (evaluate (atInput rawContext 0) xs ::ᵥ
    evaluate (atInput rawDomain 0) xs ::ᵥ evaluate (atInput rawCodomain 0) xs ::ᵥ
    evaluate (atInput rawLeast 0) xs ::ᵥ evaluate (atInput rawLeast 1) xs ::ᵥ 0 ::ᵥ nil) = _
  simp only [left, right]

private theorem candidatePacked (least : Program 3) (ctx dom cod fn arg : Nat) :
    evaluate (outputAddress least) (ctx ::ᵥ dom ::ᵥ cod ::ᵥ fn ::ᵥ arg ::ᵥ 0 ::ᵥ nil) =
      packNode 3 [ctx, cod, (evaluate least (ctx ::ᵥ cod ::ᵥ packNode 6 [dom, cod, fn, arg] ::ᵥ nil)).pred] := by
  let xs := ctx ::ᵥ dom ::ᵥ cod ::ᵥ fn ::ᵥ arg ::ᵥ 0 ::ᵥ nil
  have cell (p q : Program 6) : evaluate (consOf p q) xs = pair (evaluate p xs) (evaluate q xs) + 1 := by
    rw [consOf, compositeTwo]
    exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _
  have seedValue : evaluate seed xs = packNode 6 [dom, cod, fn, arg] := by
    have h₁ : evaluate (.projection (1 : Fin 6)) xs = dom := rfl
    have h₂ : evaluate (.projection (2 : Fin 6)) xs = cod := rfl
    have h₃ : evaluate (.projection (3 : Fin 6)) xs = fn := rfl
    have h₄ : evaluate (.projection (4 : Fin 6)) xs = arg := rfl
    have hz : evaluate (constantZero 6) xs = 0 := rfl
    simp only [seed, cell, literalEvaluation, h₁, h₂, h₃, h₄, hz, packNode, pack]
  have leastValue : evaluate (selectedLeast least) xs =
      evaluate least (ctx ::ᵥ cod ::ᵥ packNode 6 [dom, cod, fn, arg] ::ᵥ nil) := by
    change evaluate least (List.Vector.ofFn fun a : Fin 3 =>
      evaluate ((![.projection 0, .projection 2, seed] : Fin 3 → Program 6) a) xs) = _
    rw [vectorThree]
    change evaluate least (ctx ::ᵥ cod ::ᵥ evaluate seed xs ::ᵥ nil) = _
    rw [seedValue]
  have selectedValue : evaluate (selectedClass least) xs =
      (evaluate (selectedLeast least) xs).pred := by
    change evaluate predecessor (List.Vector.ofFn fun _ : Fin 1 => evaluate (selectedLeast least) xs) = _
    rw [vectorOne, exactPredecessorEvaluation]
  change evaluate addressEmitter (List.Vector.ofFn fun a : Fin 3 =>
    evaluate ((![.projection 0, .projection 2, selectedClass least] : Fin 3 → Program 6) a) xs) = _
  rw [vectorThree]
  change evaluate addressEmitter (ctx ::ᵥ cod ::ᵥ evaluate (selectedClass least) xs ::ᵥ nil) = _
  rw [exactEmitters.1, selectedValue, leastValue]
  rfl

private theorem candidateOfAccepted (s : Settings) (i : Program 1) (least : Program 3)
    (leastFit : ActualLeastCalibration s least) (f u y : Nat)
    (accepted : evaluate (applicationGuard i least) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = 1) :
    evaluate (candidateAddress least) (f ::ᵥ u ::ᵥ nil) = y := by
  have core : evaluate (applicationCore least) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = 1 := by
    rw [applicationGuard, exact_GuardEvaluation] at accepted
    split at accepted
    · rename_i h
      exact h.2.2
    · cases accepted
  let ctx := run rawContext f
  let dom := run rawDomain f
  let cod := run rawCodomain f
  let fn := run rawLeast f
  let arg := run rawLeast u
  have output := (coreAtOne least f u y).mp core
  have unit := output.2.2.2.2.2
  have bit := (exact_AllInputApplicationOutputCore s least leastFit ctx dom cod fn arg y).symm.trans unit
  have success : originalOutput s ctx dom cod fn arg = some y := by
    apply eq_of_beq
    cases h : originalOutput s ctx dom cod fn arg == some y
    · simp [h] at bit
    · rfl
  rw [candidateValue, candidatePacked, leastFit ctx cod (packNode 6 [dom, cod, fn, arg])]
  unfold originalOutput at success
  cases chosen : packedLeast s ctx cod (packNode 6 [dom, cod, fn, arg]) with
  | none => simp [chosen] at success
  | some k => simpa [chosen, encodeState] using success

theorem exact_OptionApplicationOfCalibration (s : Settings) (i : Program 1) (least : Program 3)
    (scalarFit : ActualScalarCalibration s i) (leastFit : ActualLeastCalibration s least) :
    ∀ f u, evaluate (optionApplicationOf i least) (f ::ᵥ u ::ᵥ nil) =
      Encodable.encode (application s f u) := by
  intro f u
  let xs := f ::ᵥ u ::ᵥ nil
  let candidate := candidateAddress least
  let result := evaluate candidate xs
  let check := Program.composition (applicationGuard i least) ![.projection 0, .projection 1, candidate]
  have checkValue : evaluate check xs = (graph s f u result).toNat := by
    change evaluate (applicationGuard i least) (List.Vector.ofFn fun a : Fin 3 =>
      evaluate ((![.projection 0, .projection 1, candidate] : Fin 3 → Program 2) a) xs) = _
    rw [vectorThree]
    exact exact_AllInputGuardedApplication s i least scalarFit leastFit f u result
  have positiveValue : evaluate (.composition .succ (fun _ : Fin 1 => candidate)) xs = result + 1 := by
    change evaluate .succ (List.Vector.ofFn fun _ : Fin 1 => result) = _
    rw [vectorOne]
    rfl
  change evaluate (branch check (constantZero 2) (.composition .succ (fun _ : Fin 1 => candidate))) xs = _
  rw [evalBranch, checkValue, positiveValue]
  have zero : evaluate (constantZero 2) xs = 0 := rfl
  rw [zero]
  cases selected : application s f u with
  | none => simp [graph, selected]
  | some y =>
    have accepted : evaluate (applicationGuard i least) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = 1 := by
      rw [exact_AllInputGuardedApplication s i least scalarFit leastFit f u y, graph, selected]
      simp
    have same : result = y := candidateOfAccepted s i least leastFit f u y accepted
    simp [graph, selected, same]

#print axioms exact_OptionApplicationOfCalibration

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneOptionApplicationV2
