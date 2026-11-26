module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserverFitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileObserversProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation evalBranch)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEdgeObserverFitProof (EdgeValueStable)
open NumberedWindowInternalLiteralRoundObserverTargets (observe)
open NumberedWindowInternalLiteralLeastAuxPhysicalProfileProof
  (physicalAuxProfile exact_LiteralScalarEdgePhysicalAuxProfile)
open NumberedWindowInternalLiteralAuxProfileLeastProof (functionHead functionHeadValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def unaryObserver (p : Program 1) : Program 3 :=
  .composition p (Fin.cons (.projection 2) Fin.elim0)

def maskedCoordinate (p : Program 1) : Program 1 := branch termShape (constantZero 1) p

def ProfileCoordinate (p : Program 1) : Prop :=
  p = field 0 ∨ p = field 1 ∨ p = functionHead

private theorem shapeBit (q : Nat) : run termShape q = 0 ∨ run termShape q = 1 := by
  unfold termShape nodeGood run
  rw [actualConjunctionEvaluation]
  split <;> simp

theorem exact_AuxShapeStable (s : Settings) : EdgeValueStable s (unaryObserver termShape) := by
  intro ctx ty a b g _ edge
  rw [unaryObserver,compositeOne,compositeOne]
  change run termShape a = run termShape b
  have same := exact_LiteralScalarEdgePhysicalAuxProfile s g ty a b edge
  rcases shapeBit a with no | yes <;> rcases shapeBit b with no' | yes'
  · exact no.trans no'.symm
  · simp [physicalAuxProfile,no,yes'] at same
  · simp [physicalAuxProfile,yes,no'] at same
  · exact yes.trans yes'.symm

theorem exact_AuxMaskedCoordinateStable (s : Settings) (p : Program 1) (which : ProfileCoordinate p) :
    EdgeValueStable s (unaryObserver (maskedCoordinate p)) := by
  intro ctx ty a b g _ edge
  rw [unaryObserver,compositeOne,compositeOne]
  change run (maskedCoordinate p) a = run (maskedCoordinate p) b
  have same := exact_LiteralScalarEdgePhysicalAuxProfile s g ty a b edge
  unfold maskedCoordinate run
  rw [evalBranch,evalBranch]
  change (if run termShape a = 0 then 0 else run p a) = (if run termShape b = 0 then 0 else run p b)
  rcases shapeBit a with no | yes <;> rcases shapeBit b with no' | yes'
  · simp [no,no']
  · simp [physicalAuxProfile,no,yes'] at same
  · simp [physicalAuxProfile,yes,no'] at same
  · have coords : run (field 0) a = run (field 0) b ∧
        run (field 1) a = run (field 1) b ∧ run functionHead a = run functionHead b := by
      simp only [physicalAuxProfile,yes,yes',if_pos,Option.some.injEq,Prod.mk.injEq] at same
      simpa only [functionHeadValue] using same
    have coordinate : run p a = run p b := by
      rcases which with rfl | rfl | rfl
      · exact coords.1
      · exact coords.2.1
      · exact coords.2.2
    simp [yes,yes',coordinate]

theorem exact_OpenUnaryObserverIntro (p : Program 1) (ctx ty q v : OTerm α)
    (h : D B Γ (unary p v q)) : D B Γ (observe (unaryObserver p) ctx ty q v) := by
  apply compositionValue p (Fin.cons (.projection 2) Fin.elim0) v ![ctx,ty,q] ![q] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,q]

theorem exact_OpenUnaryObserverElim (p : Program 1) (ctx ty q v : OTerm α)
    (h : D B Γ (observe (unaryObserver p) ctx ty q v)) : D B Γ (unary p v q) := by
  apply compositionRecover p (Fin.cons (.projection 2) Fin.elim0) v ![ctx,ty,q] ![q] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,q]

theorem exact_OpenMaskedCoordinateIntro (p : Program 1) (q event v : OTerm α)
    (positive : D B Γ (unary termShape (suc event) q)) (h : D B Γ (unary p v q)) :
    D B Γ (unary (maskedCoordinate p) v q) :=
  successorBranchIntro termShape (constantZero 1) p v event ![q] positive h

theorem exact_OpenMaskedCoordinateElim (p : Program 1) (q event v : OTerm α)
    (positive : D B Γ (unary termShape (suc event) q)) (h : D B Γ (unary (maskedCoordinate p) v q)) :
    D B Γ (unary p v q) :=
  successorBranchElim termShape (constantZero 1) p v event ![q] positive h

#print axioms exact_AuxShapeStable
#print axioms exact_AuxMaskedCoordinateStable
#print axioms exact_OpenUnaryObserverIntro
#print axioms exact_OpenUnaryObserverElim
#print axioms exact_OpenMaskedCoordinateIntro
#print axioms exact_OpenMaskedCoordinateElim
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileObserversProof
