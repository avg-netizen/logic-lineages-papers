module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootCallPayloadProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootPayloadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootCallLeafProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalSparseRawTick (rootCall)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root shapes)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit exact_OpenLiteralRootCaseElimination)
open NumberedWindowInternalLiteralRootCallPayloadProof (exact_OpenLiteralRootCallPayload)
open NumberedWindowInternalLiteralRootPayloadProof (exact_OpenLiteralRootPayload)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Recover the actual rule leaf and every ordered payload field of a
literal root dispatch, without presupposing a root wrapper in the
selected witness slot. The payload retains its exact physical selector
graph on the input tape. -/
theorem exact_OpenLiteralRootCallLeafCases (leaf : Nat → Program 3)
    (tape : Fin 3 → OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (rootCall (root leaf)) (suc z) tape))
    (use : ∀ tag arity, (tag,arity) ∈ shapes →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β) (fields : List (OTerm β)),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) → fields.length = arity →
      D B Δ (programGraph (frameSlot 0 1) payload (fun i => (tape i).relabel j)) →
      D B Δ (eqn payload (rawCons (numeral tag) (packedBody fields))) →
      D B Δ (bit (leaf tag) ![(tape 0).relabel j,payload,(tape 2).relabel j]) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenLiteralRootCallPayload (root leaf) tape goal held
  intro β j Δ payload keep report accepted
  apply exact_OpenLiteralRootCaseElimination leaf ![(tape 0).relabel j,payload,(tape 2).relabel j]
    (goal.relabel j) accepted
  intro tag arity known Θ extend guard selected
  apply exact_OpenLiteralRootPayload tag arity ((tape 0).relabel j) payload ((tape 2).relabel j)
    (goal.relabel j) guard
  intro γ l Ω fields stay size equation _
  let m := l ∘ j
  have all (φ : Formula α) (mem : φ ∈ Γ) : φ.relabel m ∈ Ω := by
    simpa only [m,formulaRelabelComposition] using stay _ (extend _ (keep φ mem))
  have decoded := renameInto report l Ω (fun φ mem => stay _ (extend φ mem))
  simp only [programRename,Term.relabel_relabel] at decoded
  have rule := renameInto selected l Ω stay
  simp only [bit,programRename,tripleInputsRename,sucRelabel,zRelabel,Term.relabel_relabel] at rule
  have reply := use tag arity known γ m Ω (payload.relabel l) fields all size decoded equation rule
  simpa only [m,formulaRelabelComposition] using reply

#print axioms exact_OpenLiteralRootCallLeafCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootCallLeafProof
