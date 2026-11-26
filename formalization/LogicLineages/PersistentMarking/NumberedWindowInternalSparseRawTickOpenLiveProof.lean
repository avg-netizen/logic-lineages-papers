module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenLiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (witnessShape chosenFrame)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm frameValueTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (witnessReports onTape)
open NumberedWindowInternalSparseRawFunctionFrameOpenChecks (exact_OpenLiteralFunctionFrame)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consOfGraph (p q : Program 3) (h t : OTerm α) (xs : Fin 3 → OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph p h xs)))
    (right : Nonempty (Derivation body Γ (programGraph q t xs))) :
    Nonempty (Derivation body Γ (programGraph (consOf p q) (rawCons h t) xs)) := by
  unfold consOf
  apply compositionValue fieldCons (Fin.cons p (Fin.cons q Fin.elim0)) (rawCons h t) xs ![h,t]
    (consGraph h t)
  intro i
  exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) i

private theorem scratchState (p q : Program 3) (a b : OTerm α) (xs : Fin 3 → OTerm α)
    (flag : Nonempty (Derivation body Γ (programGraph p a xs)))
    (frame : Nonempty (Derivation body Γ (programGraph q b xs))) :
    Nonempty (Derivation body Γ (programGraph (emitState p q) (stateTerm a b) xs)) := by
  have rest := consOfGraph q (constantZero 3) b z xs frame (constantZeroValue xs)
  exact consOfGraph p (consOf q (constantZero 3)) a (rawCons b z) xs flag rest

theorem literalLive (body : Positive (Fin 1)) (p other : Program 3) (α : Type)
    (dom cod arg source child dest : OTerm α) :
    Nonempty (Derivation body [] (programGraph (liveTick p other) (stateTerm z (frameValueTerm source child dest))
      ![auxiliaryTerm dom cod source arg,functionWitnessTerm child,auxiliaryTerm dom cod dest arg])) := by
  let xs : Fin 3 → OTerm α :=
    ![auxiliaryTerm dom cod source arg,functionWitnessTerm child,auxiliaryTerm dom cod dest arg]
  let f := frameValueTerm source child dest
  have tag := (witnessReports (body := body) (Γ := []) child).1
  have good : Nonempty (Derivation body [] (programGraph tagFiveTest (suc z) xs)) :=
    onTape witnessShape 1 (suc z) xs tag
  have frame := exact_OpenLiteralFunctionFrame body α dom cod arg source child dest
  have selected := scratchState (constantZero 3) chosenFrame z f xs (constantZeroValue xs) frame
  exact successorBranchIntro tagFiveTest
    (branch rootTest (emitState (constantZero 3) other) (emitState (rootCall p) (constantZero 3)))
    (emitState (constantZero 3) chosenFrame) (stateTerm z f) z xs good selected

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenLiveProof
