module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionRunPeelProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionContextChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawRun (ownRun iterateState)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)
open NumberedWindowInternalLiteralFunctionRunPeelProof

/-- The literal chosen typed parent callback is equivalent internally
to its unchanged original four outer guards and the terminal child
loop at the exact remaining fuel. This does not infer child syntax,
typing, least reports, or own-code graph convergence from a numeric
evaluation theorem. -/
theorem exact_OpenTypedFunctionRemainingFuel (body : Positive (Fin 1)) (p other window : Program 3)
    (syntaxCheck : Program 1) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg source child dst : OTerm α) :
    let xs := parentTape dom cod arg source child dst
    let ys := childTape source child dst
    let raw := programGraph (typedRaw5 p other window syntaxCheck) (suc z) ![ctx,cod,xs 0,xs 1,xs 2]
    let guards := liftedEndpointGuards window syntaxCheck ctx cod (xs 0) (xs 2)
    let terminal := programGraph (iterateState p other) (stateTerm (suc z) z)
      ![functionRemaining child,initialTerm ys]
    Nonempty (Derivation body Γ ((raw.imp (guards ⊓ terminal)) ⊓ ((guards ⊓ terminal).imp raw))) := by
  let xs := parentTape dom cod arg source child dst
  let ys := childTape source child dst
  let raw := programGraph (typedRaw5 p other window syntaxCheck) (suc z) ![ctx,cod,xs 0,xs 1,xs 2]
  let guards := liftedEndpointGuards window syntaxCheck ctx cod (xs 0) (xs 2)
  let terminal := programGraph (iterateState p other) (stateTerm (suc z) z)
    ![functionRemaining child,initialTerm ys]
  have peel := exact_OpenFunctionRemainingFuel body p other α dom cod arg source child dst z
  obtain ⟨typed⟩ := exact_OpenTypedRaw5 body p other window syntaxCheck α (raw :: Γ)
    ctx cod (xs 0) (xs 1) (xs 2)
  have hs := Derivation.implicationElimination (Derivation.conjunctionLeft typed)
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨more⟩ := closedApply
    (peel.map Derivation.conjunctionLeft)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft hs)⟩
  have fg : Derivation body (raw :: Γ) guards :=
    Derivation.conjunctionIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionLeft hs))
      (Derivation.conjunctionRight hs)
  let cup := guards ⊓ terminal
  have hc : Derivation body (cup :: Γ) cup := Derivation.hypothesis List.mem_cons_self
  have hg := Derivation.conjunctionLeft hc
  obtain ⟨run⟩ := closedApply (peel.map Derivation.conjunctionRight)
    ⟨Derivation.conjunctionRight hc⟩
  obtain ⟨back⟩ := exact_OpenTypedRaw5 body p other window syntaxCheck α (cup :: Γ)
    ctx cod (xs 0) (xs 1) (xs 2)
  have reverse := Derivation.implicationElimination (Derivation.conjunctionRight back)
    (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hg) run)
      (Derivation.conjunctionRight hg))
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction fg more))
    (Derivation.implicationIntroduction reverse)⟩

#print axioms exact_OpenTypedFunctionRemainingFuel
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionContextChecks
