module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserverFitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastGuardProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomOnEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (successorValue projectionValue compositionValue)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (edge)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (RawAtom atomicTest atomOne atomicBit)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEdgeObserverFitProof (EdgeValueStable)
open NumberedWindowInternalLiteralRoundObserverTargets (observe)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne)
open NumberedWindowAtomicLeastChecks (exact_AtomicScalarEdgeIsolation)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Zero records a non-atom, while a successor records the entire
original raw code. The distinct tags make comparison unambiguous. -/
def atomicStamp : Program 1 := branch atomicTest (constantZero 1) .succ

def atomObserver : Program 3 := .composition atomicStamp (Fin.cons (.projection 2) Fin.elim0)

private theorem leftNotAtomic (s : NumberedWindowScalarAlgorithm.Settings)
    (g : List Nat) (ty a b : Nat) (yes : edge s g ty a b = true) : run atomicTest a = 0 := by
  rcases atomicBit a with no | on
  · exact no
  · rcases (atomOne a).mp on with ⟨t,n,rfl⟩ | ⟨t,rfl⟩
    · have h := ((exact_AtomicScalarEdgeIsolation s g ty t).1 n b).1
      rw [h] at yes
      contradiction
    · have h := ((exact_AtomicScalarEdgeIsolation s g ty t).2 b).1
      rw [h] at yes
      contradiction

private theorem rightNotAtomic (s : NumberedWindowScalarAlgorithm.Settings)
    (g : List Nat) (ty a b : Nat) (yes : edge s g ty a b = true) : run atomicTest b = 0 := by
  rcases atomicBit b with no | on
  · exact no
  · rcases (atomOne b).mp on with ⟨t,n,rfl⟩ | ⟨t,rfl⟩
    · have h := ((exact_AtomicScalarEdgeIsolation s g ty t).1 n a).2
      rw [h] at yes
      contradiction
    · have h := ((exact_AtomicScalarEdgeIsolation s g ty t).2 a).2
      rw [h] at yes
      contradiction

theorem exact_AtomicObserverStable (s : NumberedWindowScalarAlgorithm.Settings) : EdgeValueStable s atomObserver := by
  intro ctx ty a b g _ yes
  rw [atomObserver,compositeOne,compositeOne]
  change run atomicStamp a = run atomicStamp b
  unfold atomicStamp run
  rw [evalBranch,evalBranch]
  change (if run atomicTest a = 0 then 0 else _) = (if run atomicTest b = 0 then 0 else _)
  simp only [leftNotAtomic s g ty a b yes, rightNotAtomic s g ty a b yes]
  rfl

theorem exact_OpenAtomStampZero (q : OTerm α) (no : D B Γ (unary atomicTest z q)) :
    D B Γ (unary atomicStamp z q) :=
  zeroBranchIntro atomicTest (constantZero 1) .succ z ![q] no (zeroConstantValue ![q])

theorem exact_OpenAtomStampPositive (q event : OTerm α) (yes : D B Γ (unary atomicTest (suc event) q)) :
    D B Γ (unary atomicStamp (suc q) q) :=
  successorBranchIntro atomicTest (constantZero 1) .succ (suc q) event ![q] yes (successorValue ![q])

theorem exact_OpenAtomObserverIntro (ctx ty q stamp : OTerm α) (v : D B Γ (unary atomicStamp stamp q)) :
    D B Γ (observe atomObserver ctx ty q stamp) := by
  apply compositionValue atomicStamp (Fin.cons (.projection 2) Fin.elim0) stamp ![ctx,ty,q] ![q] v
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,q]

theorem exact_OpenAtomObserverElim (ctx ty q stamp : OTerm α) (v : D B Γ (observe atomObserver ctx ty q stamp)) :
    D B Γ (unary atomicStamp stamp q) := by
  apply compositionRecover atomicStamp (Fin.cons (.projection 2) Fin.elim0) stamp ![ctx,ty,q] ![q] v
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,q]

#print axioms exact_AtomicObserverStable
#print axioms exact_OpenAtomStampZero
#print axioms exact_OpenAtomStampPositive
#print axioms exact_OpenAtomObserverIntro
#print axioms exact_OpenAtomObserverElim
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomOnEdgeProof
