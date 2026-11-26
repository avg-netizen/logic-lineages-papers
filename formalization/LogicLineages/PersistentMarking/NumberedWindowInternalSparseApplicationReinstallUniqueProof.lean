module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallReportCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenCallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChooseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallUniqueProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawDomain rawCodomain rawLeast)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (slotRead slotIntro)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendOpenGateProof (G args readGuard readCore)
open NumberedWindowInternalSparseApplicationFrontendOpenCallProof (Slot readOutput)
open NumberedWindowInternalSparseApplicationFrontendOpenChooseProof (Observed choose)
open NumberedWindowInternalSparseApplicationReinstallReportCasesProof (coherent)
open NumberedWindowInternalSparseApplicationReinstallTargets

private theorem acceptsGraph {α : Type} (p : Program 3) (f u y : OTerm α) :
    accepts p f u y = programGraph p (suc z) ![f,u,y] := rfl

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem copySlot (p : Program 1) (idx : Fin 3) (v : OTerm α)
    (before after : Fin 3 → OTerm α) (sameInput : before idx = after idx)
    (observed : Slot body Γ p idx v before) : Slot body Γ p idx v after := by
  have read : Nonempty (Derivation body Γ (unary p v (after idx))) := by
    rw [← sameInput]
    exact slotRead p idx v before observed
  exact slotIntro p idx v after read

private theorem withSelectors (i : Program 1) (least : Program 3) (f u y w : OTerm α)
    (ys : Fin 8 → OTerm α) (observed : Observed body Γ (args f u y) ys)
    (left : G body Γ (applicationGuard i least) (args f u y))
    (right : G body Γ (applicationGuard i least) (args f u w)) :
    Nonempty (Derivation body Γ (eqn y w)) := by
  let xs := args f u y
  let ws := args f u w
  have lh := readCore least xs (readGuard i least f u y left).2.2
  have rh := readCore least ws (readGuard i least f u w right).2.2
  let c := ys 0
  let d := ys 2
  let e := ys 3
  let fn := ys 4
  let arg := ys 7
  have l := readOutput least xs c d e fn arg (observed 0) (observed 2) (observed 3)
    (observed 4) (observed 7) lh.output
  have r := readOutput least ws c d e fn arg
    (copySlot rawContext 0 c xs ws rfl (observed 0))
    (copySlot rawDomain 0 d xs ws rfl (observed 2))
    (copySlot rawCodomain 0 e xs ws rfl (observed 3))
    (copySlot rawLeast 0 fn xs ws rfl (observed 4))
    (copySlot rawLeast 1 arg xs ws rfl (observed 7)) rh.output
  exact coherent least c e _ y w l r

private theorem movedGuard (i : Program 1) (least : Program 3) (f u y : OTerm α)
    (known : G body Γ (applicationGuard i least) (args f u y))
    (β : Type) (j : α → β) (Δ : List (Formula β))
    (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ) :
    G body Δ (applicationGuard i least) (args (f.relabel j) (u.relabel j) (y.relabel j)) := by
  have moved := renameInto known j Δ keep
  change Nonempty (Derivation body Δ
    ((programGraph (applicationGuard i least) (suc z) ![f,u,y]).relabel j)) at moved
  rw [graph3Rename,sucRelabel,zRelabel] at moved
  exact moved

theorem unique : ExactUniqueGuardedApplication := by
  intro i least body α Γ f u y w left right
  rw [acceptsGraph] at left right
  rw [equalEqn]
  apply choose f u y (eqn y w)
  intro β j Δ ys keep observed
  rw [eqnRelabel]
  exact withSelectors i least (f.relabel j) (u.relabel j) (y.relabel j) (w.relabel j) ys observed
    (movedGuard i least f u y left β j Δ keep) (movedGuard i least f u w right β j Δ keep)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallUniqueProof
