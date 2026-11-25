module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRawSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRootSuccessProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawRun (iterateState)
open NumberedWindowInternalSparseRawTick (rootCall stateFrame rowSource rowWitness rowDestination)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)
open NumberedWindowInternalLiteralPhysicalUnderlyingReportsProof (exact_OpenPhysicalUnderlyingReports)
open NumberedWindowInternalLiteralTypedRawSuccessProof (exact_OpenLiteralTypedRawSuccessCases)

variable {α : Type} {Γ : List (Formula α)}

/-- Recover a successful root callback of the original installed body
from a direct edge alone. The reported initial tape comes from the
actual direct certificate, and the rooted tape may be reached after
contextual steps. All derivations live in the same ordinary body. -/
theorem exact_OpenLiteralDirectRootSuccessCases (i cv tv : Program 1)
    (p other window L : Program 3) (V : Program 1) (c : Nat)
    (x y : OTerm α) (goal : Formula α) :
    let raw := typedRaw5 p other window V
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    D B Γ (direct data (hop cv tv R L) c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (q w r u prev frame : OTerm β) (tape : Fin 3 → OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (programGraph (iterateState p other) prev ![u,stateTerm z (frameValueTerm q w r)]) →
      D B Δ (unary stateFrame (suc frame) prev) →
      D B Δ (unary rowSource (tape 0) prev) →
      D B Δ (unary rowWitness (tape 1) prev) →
      D B Δ (unary rowDestination (tape 2) prev) →
      D B Δ (programGraph (rootCall p) (suc z) tape) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro raw R data B edge use
  apply exact_OpenPhysicalUnderlyingReports i cv tv raw L c x y goal edge
  intro β j Δ ctx ty before after cert q w r keep _ _ _ _ _ calls
  obtain ⟨row⟩ := calls
  have accepted := Derivation.conjunctionLeft (Derivation.conjunctionRight row)
  apply exact_OpenLiteralTypedRawSuccessCases p other window V ctx ty q w r (goal.relabel j) ⟨accepted⟩
  intro γ l Ω u prev frame tape stay run live left path right hit
  let m := l ∘ j
  have retain (φ : Formula α) (mem : φ ∈ Γ) : φ.relabel m ∈ Ω := by
    simpa only [m,formulaRelabelComposition] using stay _ (keep φ mem)
  simp only [stateRename,frameValueTerm,sucRelabel,rawConsRename,zRelabel] at run
  have reply := use γ m Ω (q.relabel l) (w.relabel l) (r.relabel l) u prev frame tape retain
    run live left path right hit
  simpa only [m,formulaRelabelComposition] using reply

#print axioms exact_OpenLiteralDirectRootSuccessCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectRootSuccessProof
