module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderTransitivity)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalSquareRootArithmetic (square)
open ID1Completion.InternalUnpairArithmeticProof (leftWeakAdd)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (rightWeakAdd weakTrans squareSelfWeak)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets
  (auxiliaryTerm functionWitnessTerm frameValueTerm)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenChecks (exact_OpenLiftedTick)
open NumberedWindowInternalSparseRawRun (initialState iterateState ownState ownRun)
open NumberedWindowInternalSparseRawRunShapeOwnProof (initialGraph)
open NumberedWindowInternalSparseRawRunSuccessProof (ownRunTerminal terminalOwnRun)
open NumberedWindowInternalSparseRawRunLiftProof (runLift)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The cons head is strictly below the sparse cons code. -/
theorem headLess (x t : OTerm α) : Nonempty (Derivation body Γ (ltF x (rawCons x t))) :=
  rightWeakAdd (square (add x t)) x

/-- The cons tail is strictly below the sparse cons code. -/
theorem tailLess (x t : OTerm α) : Nonempty (Derivation body Γ (ltF t (rawCons x t))) := by
  let s := add x t
  exact weakTrans t (square s) (pairTerm x t)
    (weakTrans t s (square s) (rightWeakAdd x t) (squareSelfWeak s))
    (leftWeakAdd (square s) x)

theorem witnessStrict (child : OTerm α) :
    Nonempty (Derivation body Γ (ltF child (functionWitnessTerm child))) := by
  let inner : OTerm α := rawCons child z
  obtain ⟨one⟩ := headLess (body := body) (Γ := Γ) child z
  obtain ⟨two⟩ : Nonempty (Derivation body Γ (ltF inner (functionWitnessTerm child))) :=
    tailLess _ inner
  exact closedApply (actualOriginalOrderTransitivity body α child inner (functionWitnessTerm child))
    ⟨Derivation.conjunctionIntroduction one two⟩

/-- Initial scratch term of an arbitrary ternary tape. -/
abbrev initialTerm (xs : Fin 3 → OTerm α) : OTerm α :=
  stateTerm z (frameValueTerm (xs 0) (xs 1) (xs 2))

/-- Peel the actual own state down to its loop at the literal initial
scratch, with fuel the tape's own witness slot. -/
theorem ownLoop (p other : Program 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (ownState p other) out xs))) :
    Nonempty (Derivation body Γ
      (programGraph (iterateState p other) out ![xs 1,initialTerm xs])) := by
  apply compositionRecover (iterateState p other) ![.projection 1,initialState] out xs
    ![xs 1,initialTerm xs] h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (initialGraph xs) (fun e => Fin.elim0 e)) i

theorem loopOwn (p other : Program 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ
      (programGraph (iterateState p other) out ![xs 1,initialTerm xs]))) :
    Nonempty (Derivation body Γ (programGraph (ownState p other) out xs)) := by
  apply compositionValue (iterateState p other) ![.projection 1,initialState] out xs
    ![xs 1,initialTerm xs] h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (initialGraph xs) (fun e => Fin.elim0 e)) i

/-- General own-run lift: a genuine tick from the parent's initial scratch
to the child's, the child's witness strictly below the parent's in the
original object order, and a successful child own run. -/
theorem ownRunLift (p other : Program 3) (k : OTerm α) (xs ys : Fin 3 → OTerm α)
    (ht : Nonempty (Derivation body Γ
      (programGraph (chosenTick p other) (initialTerm ys) ![initialTerm xs])))
    (hlt : Nonempty (Derivation body Γ (ltF (ys 1) (xs 1))))
    (h : Nonempty (Derivation body Γ (programGraph (ownRun p other) (suc k) ys))) :
    Nonempty (Derivation body Γ (programGraph (ownRun p other) (suc k) xs)) := by
  have childState := ownRunTerminal p other k ys h
  have childLoop := ownLoop p other (stateTerm (suc k) z) ys childState
  have parentLoop := runLift p other (suc k) (initialTerm xs) (initialTerm ys) (ys 1) (xs 1)
    ht hlt childLoop
  exact terminalOwnRun p other k xs (loopOwn p other (stateTerm (suc k) z) xs parentLoop)

theorem liftedOwnRun (p other : Program 3) (dom cod arg source child dest k : OTerm α)
    (h : Nonempty (Derivation body Γ
      (programGraph (ownRun p other) (suc k) ![source,child,dest]))) :
    Nonempty (Derivation body Γ (programGraph (ownRun p other) (suc k)
      ![auxiliaryTerm dom cod source arg,functionWitnessTerm child,
        auxiliaryTerm dom cod dest arg])) := by
  obtain ⟨tick⟩ := exact_OpenLiftedTick body p other α z dom cod arg source child dest
  exact ownRunLift p other k
    ![auxiliaryTerm dom cod source arg,functionWitnessTerm child,auxiliaryTerm dom cod dest arg]
    ![source,child,dest] ⟨weakenClosed tick Γ⟩ (witnessStrict child) h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
