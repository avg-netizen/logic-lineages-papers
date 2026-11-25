module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOwnRawSuccessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRawSuccessProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawRun (iterateState)
open NumberedWindowInternalSparseRawTick (rootCall stateFrame rowSource rowWitness rowDestination)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)
open NumberedWindowInternalLiteralOwnRawSuccessProof (exact_OpenLiteralOwnRawSuccessCases)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An accepted typed raw callback yields a genuine earlier root call
even when the original witness is open and not a literal root wrapper.
All programs and the first scratch are those of the actual typed raw
checker; no fixed-root or fixed witness length premise is needed. -/
theorem exact_OpenLiteralTypedRawSuccessCases (p other window : Program 3) (V : Program 1)
    (ctx ty q w r : OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (typedRaw5 p other window V) (suc z) ![ctx,ty,q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (u prev frame : OTerm β) (tape : Fin 3 → OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (programGraph (iterateState p other) prev
        ![u,(stateTerm z (frameValueTerm q w r)).relabel j]) →
      D B Δ (unary stateFrame (suc frame) prev) →
      D B Δ (unary rowSource (tape 0) prev) →
      D B Δ (unary rowWitness (tape 1) prev) →
      D B Δ (unary rowDestination (tape 2) prev) →
      D B Δ (programGraph (rootCall p) (suc z) tape) →
      D B Δ (goal.relabel j)) :
    D B Γ goal := by
  obtain ⟨codec⟩ := exact_OpenTypedRaw5 B p other window V α Γ ctx ty q w r
  obtain ⟨h⟩ := held
  have checks := Derivation.implicationElimination (Derivation.conjunctionLeft codec) h
  have run := Derivation.conjunctionRight (Derivation.conjunctionLeft checks)
  apply exact_OpenLiteralOwnRawSuccessCases p other q w r z goal ⟨run⟩
  intro β j Δ u prev frame tape keep prior available left path right hit
  rw [zRelabel] at hit
  exact use β j Δ u prev frame tape keep prior available left path right hit

#print axioms exact_OpenLiteralTypedRawSuccessCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRawSuccessProof
