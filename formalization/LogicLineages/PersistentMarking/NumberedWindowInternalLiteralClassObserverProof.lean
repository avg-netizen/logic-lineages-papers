module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileObserversProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassObserverProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathEnvelope (nodeGood run)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration packedLeast encodeState)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEdgeObserverFitProof (EdgeValueStable)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralRoundObserverTargets (observe)
open NumberedWindowInternalLiteralAuxClassLeastProof (functionClass argumentClass functionClassValue argumentClassValue)
open NumberedWindowInternalLiteralNumericAuxClassesProof (auxClasses exact_LiteralAuxClassEdge)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne compositeTwo)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def classRead (P : Program 2) : Program 3 :=
  .composition P (Fin.cons (.projection 0) (Fin.cons (.projection 2) Fin.elim0))

/-- Mask an independent typed child callback outside the auxiliary
branch. The comparator's AST is a parameter independent of the
output-producing packed minimum whose rounds may use this observer. -/
def classObserver (P : Program 2) : Program 3 :=
  branch (unaryObserver termShape) (constantZero 3) (classRead P)

private theorem shapeBit (q : Nat) : run termShape q = 0 ∨ run termShape q = 1 := by
  unfold termShape nodeGood run
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem stableClass (s : Settings) (cover : WindowSeedsCovered s)
    (symmetry : HeadPairsSymmetric s.equivalentHeads) (K : Program 3)
    (fit : ActualLeastCalibration s K) (P : Program 2)
    (which : P = functionClass K ∨ P = argumentClass K) : EdgeValueStable s (classObserver P) := by
  intro ctx ty a b g parsed edge
  have shape := exact_AuxShapeStable s ctx ty a b g parsed edge
  change run termShape a = run termShape b at shape
  have equal := exact_LiteralAuxClassEdge s cover symmetry g ty a b edge
  unfold classObserver classRead unaryObserver
  rw [evalBranch,evalBranch,compositeOne,compositeOne,compositeTwo,compositeTwo]
  change (if run termShape a = 0 then 0 else evaluate P (ctx ::ᵥ a ::ᵥ nil)) =
    (if run termShape b = 0 then 0 else evaluate P (ctx ::ᵥ b ::ᵥ nil))
  rcases shapeBit a with no | yes
  · rw [no,← shape,no] <;> rfl
  · have yes' := shape.symm.trans yes
    obtain ⟨d,c,f,u,ha⟩ := (termOne a).mp yes
    obtain ⟨d',c',f',u',hb⟩ := (termOne b).mp yes'
    simp only [auxClasses,ha,hb,Option.some.injEq,Prod.mk.injEq] at equal
    obtain ⟨de,ce,fEq,aEq⟩ := equal
    subst d'
    subst c'
    have h : evaluate P (ctx ::ᵥ a ::ᵥ nil) = evaluate P (ctx ::ᵥ b ::ᵥ nil) := by
      rcases which with rfl | rfl
      · rw [functionClassValue K ctx a d c f u ha,functionClassValue K ctx b d c f' u' hb,fit,fit]
        simp only [packedLeast,parsed,Option.bind_some,fEq]
      · rw [argumentClassValue K ctx a d c f u ha,argumentClassValue K ctx b d c f' u' hb,fit,fit]
        simp only [packedLeast,parsed,Option.bind_some,aEq]
    simp [yes,yes',h]

theorem exact_FunctionClassObserverStable (s : Settings) (cover : WindowSeedsCovered s)
    (symmetry : HeadPairsSymmetric s.equivalentHeads) (K : Program 3) (fit : ActualLeastCalibration s K) :
    EdgeValueStable s (classObserver (functionClass K)) :=
  stableClass s cover symmetry K fit _ (Or.inl rfl)

theorem exact_ArgumentClassObserverStable (s : Settings) (cover : WindowSeedsCovered s)
    (symmetry : HeadPairsSymmetric s.equivalentHeads) (K : Program 3) (fit : ActualLeastCalibration s K) :
    EdgeValueStable s (classObserver (argumentClass K)) :=
  stableClass s cover symmetry K fit _ (Or.inr rfl)

private theorem readIntro (P : Program 2) (ctx ty raw out : OTerm α)
    (h : D B Γ (programGraph P out ![ctx,raw])) :
    D B Γ (observe (classRead P) ctx ty raw out) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,raw]
  apply compositionValue P (Fin.cons (.projection 0) (Fin.cons (.projection 2) Fin.elim0)) out xs ![ctx,raw] h
  exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 2 xs) (fun bad => Fin.elim0 bad)) i

private theorem readElim (P : Program 2) (ctx ty raw out : OTerm α)
    (h : D B Γ (observe (classRead P) ctx ty raw out)) :
    D B Γ (programGraph P out ![ctx,raw]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,raw]
  apply compositionRecover P (Fin.cons (.projection 0) (Fin.cons (.projection 2) Fin.elim0)) out xs ![ctx,raw] h
  exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 2 xs) (fun bad => Fin.elim0 bad)) i

theorem exact_OpenActiveClassObserverIntro (P : Program 2) (ctx ty raw event out : OTerm α)
    (shape : D B Γ (unary termShape (suc event) raw))
    (held : D B Γ (programGraph P out ![ctx,raw])) :
    D B Γ (observe (classObserver P) ctx ty raw out) :=
  successorBranchIntro (unaryObserver termShape) (constantZero 3) (classRead P) out event ![ctx,ty,raw]
    (exact_OpenUnaryObserverIntro termShape ctx ty raw (suc event) shape) (readIntro P ctx ty raw out held)

theorem exact_OpenActiveClassObserverElim (P : Program 2) (ctx ty raw event out : OTerm α)
    (shape : D B Γ (unary termShape (suc event) raw))
    (held : D B Γ (observe (classObserver P) ctx ty raw out)) :
    D B Γ (programGraph P out ![ctx,raw]) :=
  readElim P ctx ty raw out
    (successorBranchElim (unaryObserver termShape) (constantZero 3) (classRead P) out event ![ctx,ty,raw]
      (exact_OpenUnaryObserverIntro termShape ctx ty raw (suc event) shape) held)

#print axioms exact_FunctionClassObserverStable
#print axioms exact_ArgumentClassObserverStable
#print axioms exact_OpenActiveClassObserverIntro
#print axioms exact_OpenActiveClassObserverElim
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralClassObserverProof
