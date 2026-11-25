module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastGuardProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgram (literal predOne compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne compositeTwo literalEvaluation predEvaluation compareEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest freeCode bottomCode)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration packedLeast encodeState)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowAtomicLeastChecks (exact_AtomicLeastSingleton)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (Settings least)

def atomicTest : Program 1 := branch freeTest bottomTest (literal 1 1)

def pairFirst (p : Program 1) : Program 2 := .composition p (Fin.cons (.projection 0) Fin.elim0)
def pairSecond (p : Program 1) : Program 2 := .composition p (Fin.cons (.projection 1) Fin.elim0)
def outRaw : Program 2 := pairSecond predOne
def outAtom : Program 2 := .composition atomicTest (Fin.cons outRaw Fin.elim0)
def checkAtom : Program 2 := branch (pairFirst atomicTest) outAtom (literal 2 1)
def checkSame : Program 2 :=
  .composition compareNumbers (Fin.cons (.projection 0) (Fin.cons outRaw Fin.elim0))
def keepAtom : Program 2 := branch checkSame (constantZero 2) (.projection 1)
def atomOutput : Program 2 := branch checkAtom (.projection 1) keepAtom

/-- Select a real validator on the input and the decoded output of the
original packed least program. If either term is an atom, keep a
nonzero result only when the original input equals the decoded result.
No changes are made to the original context/type selection. -/
def guardedLeast (L : Program 3) : Program 3 :=
  .composition atomOutput (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))

def RawAtom (q : Nat) : Prop := (∃ t n, q = freeRaw t n) ∨ (∃ t, q = bottomRaw t)

private theorem nodeBit (tag arity q : Nat) :
    run (nodeGood (literal 1 tag) arity) q = 0 ∨ run (nodeGood (literal 1 tag) arity) q = 1 := by
  unfold run nodeGood
  rw [conjunctionEvaluation]
  split <;> simp

theorem atomicBit (q : Nat) : run atomicTest q = 0 ∨ run atomicTest q = 1 := by
  unfold run atomicTest
  simp only [evalBranch]
  change (if run freeTest q = 0 then run bottomTest q else evaluate (literal 1 1) (q ::ᵥ nil)) = 0 ∨
    (if run freeTest q = 0 then run bottomTest q else evaluate (literal 1 1) (q ::ᵥ nil)) = 1
  rw [literalEvaluation]
  split
  · exact nodeBit 3 1 q
  · exact Or.inr rfl

theorem atomOne (q : Nat) : run atomicTest q = 1 ↔ RawAtom q := by
  unfold atomicTest run
  rw [evalBranch,literalEvaluation]
  change (if run freeTest q = 0 then run bottomTest q else 1) = 1 ↔ RawAtom q
  rcases nodeBit 0 2 q with off | on
  · have hf : run freeTest q = 0 := off
    rw [hf,if_pos rfl,bottomCode]
    constructor
    · exact Or.inr
    · intro h
      rcases h with free | bottom
      · have bad := (freeCode q).mpr free
        rw [hf] at bad
        exact False.elim (Nat.zero_ne_one bad)
      · exact bottom
  · have hf : run freeTest q = 1 := on
    rw [hf,if_neg (by decide : (1 : Nat) ≠ 0)]
    exact ⟨fun _ => Or.inl ((freeCode q).mp hf),fun _ => rfl⟩

private theorem outputValue (q s : Nat) : evaluate outRaw (q ::ᵥ s ::ᵥ nil) = s.pred := by
  unfold outRaw pairSecond
  rw [compositeOne]
  exact predEvaluation s

theorem checkAtomValue (q s : Nat) : evaluate checkAtom (q ::ᵥ s ::ᵥ nil) =
    if run atomicTest q = 0 then run atomicTest s.pred else 1 := by
  rw [checkAtom,evalBranch,pairFirst,outAtom,compositeOne,compositeOne,outputValue,literalEvaluation]
  rfl

theorem checkSameValue (q s : Nat) : evaluate checkSame (q ::ᵥ s ::ᵥ nil) =
    if q = s.pred then 1 else 0 := by
  rw [checkSame,compositeTwo,outputValue]
  exact compareEvaluation q s.pred

theorem outputGuardValue (q s : Nat) : evaluate atomOutput (q ::ᵥ s ::ᵥ nil) =
    if run atomicTest q = 1 ∨ run atomicTest s.pred = 1 then
      (if q = s.pred then s else 0)
    else s := by
  have project : evaluate (.projection (1 : Fin 2)) (q ::ᵥ s ::ᵥ nil) = s := rfl
  have zero : evaluate (constantZero 2) (q ::ᵥ s ::ᵥ nil) = 0 := rfl
  rw [atomOutput,evalBranch,checkAtomValue,keepAtom,evalBranch,checkSameValue,project,zero]
  rcases atomicBit q with a0 | a1
  · rw [a0]
    rcases atomicBit s.pred with b0 | b1
    · rw [b0]; simp
    · rw [b1]; by_cases h : q = s.pred <;> simp [h]
  · rw [a1]; by_cases h : q = s.pred <;> simp [h]

private theorem singletonInput (s : Settings) (ctx ty q t : Nat)
    (held : packedLeast s ctx ty q = some t) (atom : RawAtom q ∨ RawAtom t) : q = t := by
  unfold packedLeast at held
  cases hc : unpack ctx with
  | none => simp [hc] at held
  | some g =>
    have value : least s g ty q = some t := by simpa only [hc,Option.bind_some] using held
    rcases atom with (⟨a,n,h⟩ | ⟨a,h⟩) | (⟨a,n,h⟩ | ⟨a,h⟩)
    · subst q
      exact (((exact_AtomicLeastSingleton s g ty a).1 n).2 t value).symm
    · subst q
      exact ((exact_AtomicLeastSingleton s g ty a).2.2 t value).symm
    · subst t
      exact ((exact_AtomicLeastSingleton s g ty a).1 n).1 q value
    · subst t
      exact (exact_AtomicLeastSingleton s g ty a).2.1 q value

/-- The new actual least AST is calibrated for every packed input.
This uses the independent numerical singleton result only at the
calibration boundary, not as an internal object deduction. -/
theorem exact_LiteralAtomicGuardedLeast (s : Settings) (L : Program 3)
    (cal : ActualLeastCalibration s L) : ActualLeastCalibration s (guardedLeast L) := by
  intro ctx ty q
  rw [guardedLeast,compositeTwo,cal ctx ty q]
  change evaluate atomOutput (q ::ᵥ encodeState (packedLeast s ctx ty q) ::ᵥ nil) = _
  rw [outputGuardValue]
  cases hp : packedLeast s ctx ty q with
  | none => simp [encodeState]
  | some t =>
    change (if run atomicTest q = 1 ∨ run atomicTest t = 1 then
      (if q = t then t + 1 else 0) else t + 1) = t + 1
    by_cases atom : run atomicTest q = 1 ∨ run atomicTest t = 1
    · have paired : RawAtom q ∨ RawAtom t := atom.imp ((atomOne q).mp) ((atomOne t).mp)
      simp [singletonInput s ctx ty q t hp paired]
    · simp [atom]

#print axioms exact_LiteralAtomicGuardedLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastGuardProof
