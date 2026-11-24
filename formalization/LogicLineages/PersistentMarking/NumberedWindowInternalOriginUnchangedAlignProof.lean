module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginUnchangedAlignTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginUnchangedAlignProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalOriginBothRemovedNonemptyTargets (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalOriginUnchangedAlignTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveTail (p : Program 2) (out kept fromSlot toSlot : OTerm α)
    (same : D B Γ (eqn fromSlot toSlot))
    (given : D B Γ (programGraph p out ![kept,fromSlot])) :
    D B Γ (programGraph p out ![kept,toSlot]) := by
  unfold programGraph at given ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula p)
    out ![kept,fromSlot] ![kept,toSlot] _ given
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change D B Γ (equal kept kept)
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl kept⟩
  · obtain rfl := Fin.eq_zero j
    change D B Γ (equal fromSlot toSlot)
    rw [equalEqn]
    exact same

theorem exact_OpenOriginUnchangedJoinedEq : ExactOpenOriginUnchangedJoinedEq := by
  intro B α Γ kept removed projected sourceJoin targetJoin emptyRemoved emptyProjected sourceApp targetApp
  have origin := moveTail append sourceJoin kept removed z emptyRemoved sourceApp
  have successor := moveTail append targetJoin kept projected z emptyProjected targetApp
  exact valueUnique append sourceJoin targetJoin ![kept,z] origin successor

/-- No replacement code is chosen for the unchanged side. Transfer the
literal original source's count report to the very observed target join. -/
theorem exact_OpenOriginUnchangedAlign : ExactOpenOriginUnchangedAlign := by
  intro B α Γ source kept removed projected sourceJoin targetJoin emptyRemoved emptyProjected sourceApp targetApp accepted
  have e := exact_OpenOriginUnchangedJoinedEq B α Γ kept removed projected sourceJoin targetJoin
    emptyRemoved emptyProjected sourceApp targetApp
  exact moveTail permutation (suc z) source sourceJoin targetJoin e accepted

#print axioms exact_OpenOriginUnchangedJoinedEq
#print axioms exact_OpenOriginUnchangedAlign

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginUnchangedAlignProof
