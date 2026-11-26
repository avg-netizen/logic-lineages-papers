module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRootSuccessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootCallPayloadProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalSparseRawTick (rootCall)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Decode exactly the selected payload of an arbitrary accepted root
call. This inverts the physical normalizer and retains the original
source and target on the same tape. Unlike literal-wrapper inversion,
it does not preassign the term in the witness slot. -/
theorem exact_OpenLiteralRootCallPayload (p : Program 3) (tape : Fin 3 → OTerm α)
    (goal : Formula α)
    (held : D B Γ (programGraph (rootCall p) (suc z) tape))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (programGraph (frameSlot 0 1) payload (fun i => (tape i).relabel j)) →
      D B Δ (programGraph p (suc z) ![(tape 0).relabel j,payload,(tape 2).relabel j]) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply programCases (frameSlot 0 1) tape goal
  intro β j Δ payload keep report
  let xs := fun i => (tape i).relabel j
  let selectors : Fin 3 → Program 3 := ![.projection 0,frameSlot 0 1,.projection 2]
  have success := renameInto held j Δ keep
  simp only [programRename,sucRelabel,zRelabel] at success
  have run := normalizeRecover (.composition p selectors) xs success
  have accepted : D B Δ (programGraph p (suc z) ![xs 0,payload,xs 2]) := by
    apply compositionRecover p selectors (suc z) xs ![xs 0,payload,xs 2] run
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases report (Fin.cases (projectionValue 2 xs) (fun e => Fin.elim0 e))) i
  exact use β j Δ payload keep report accepted

#print axioms exact_OpenLiteralRootCallPayload
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootCallPayloadProof
