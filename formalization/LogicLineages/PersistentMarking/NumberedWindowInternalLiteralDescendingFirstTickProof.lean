module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingTickSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionFrameInversionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingFirstTickProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTick (rootTest rootCall)
open NumberedWindowInternalSparseRawRunLiftOwnProof (witnessStrict)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (D)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt exact_OpenPhysicalFirstTickCases)
open NumberedWindowInternalLiteralDescendingTickSupportProof
  (tickFrameCases tickFrame tickRename moveOrderRight)
open NumberedWindowInternalLiteralFunctionFrameInversionProof (exact_OpenFunctionFrameInversion)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralBoundedFallbackOpenProof (exact_OpenDescendingFallbackParts)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def FrameDecoder (C : Program 3) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q w r n : OTerm α) (goal : Formula α),
    D B Γ (programGraph C (suc n) ![q,w,r]) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (x v y : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (suc (n.relabel j)) (frameValueTerm x v y)) →
      D B Δ (ltF v (w.relabel j)) → D B Δ (goal.relabel j)) →
    D B Γ goal

theorem functionDecoder : FrameDecoder chosenFrame := by
  intro B α Γ q w r n goal h use
  apply exact_OpenFunctionFrameInversion q w r n goal h
  intro β j Δ dom cod x arg v dom' cod' y arg' keep parts equal
  obtain ⟨witness⟩ := parts.witness
  have smaller := moveOrderRight v _ (w.relabel j) (witnessStrict v) ⟨symm witness⟩
  exact use β j Δ x v y keep equal smaller

theorem fallbackDecoder (other : Program 3) : FrameDecoder (fallback other) :=
  fun _ _ _ q w r n goal h use => exact_OpenDescendingFallbackParts other q w r n goal h use

private theorem frameTransition (p other C : Program 3) (q w r frame : OTerm α) (goal : Formula α)
    (decode : FrameDecoder C)
    (call : D B Γ (programGraph C frame ![q,w,r]))
    (step : D B Γ (TickAt p other z frame q w r))
    (reject : ∀ Δ : List (Formula α), (∀ f ∈ Γ, f ∈ Δ) →
      D B Δ (TickAt p other z z q w r) → D B Δ goal)
    (child : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (x v y : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (ltF v (w.relabel j)) →
      D B Δ (TickAt p other z (frameValueTerm x v y) (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply tickFrameCases p other q w r frame goal step reject
  intro β j Δ n keep equal tick
  have moved := renameInto call j Δ keep
  rw [programRename,tripleInputsRename] at moved
  let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  have atN := outputTransport C (frame.relabel j) (suc n) xs equal moved
  apply decode B β Δ (q.relabel j) (w.relabel j) (r.relabel j) n (goal.relabel j) atN
  intro γ k Ω x v y stay val lt
  have ht := renameInto tick k Ω stay
  rw [tickRename,zRelabel,sucRelabel] at ht
  have canon := tickFrame p other z (suc (n.relabel k)) (frameValueTerm x v y)
    ((q.relabel j).relabel k) ((w.relabel j).relabel k) ((r.relabel j).relabel k) ht val
  have all (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
    simpa only [formulaRelabelComposition] using stay _ (keep f hf)
  have out := child γ (k ∘ j) Ω x v y all
    (by simpa only [Term.relabel_relabel] using lt) (by simpa only [Term.relabel_relabel] using canon)
  simpa only [formulaRelabelComposition] using out

/-- The actual executable first tick, with a structural decoder
for the supplied fallback, either reaches a root terminal flag, rejects with
zero, or steps to an exact raw child with a strictly smaller witness.
Only the structural fallback decoder is assumed. -/
theorem exact_OpenDescendingFirstTickWith (p other : Program 3) (otherDecodes : FrameDecoder other) (q w r : OTerm α)
    (goal : Formula α)
    (root : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (flag : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (bit rootTest ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (programGraph (rootCall p) flag ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (TickAt p other flag z (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j))
    (reject : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (TickAt p other z z (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j))
    (child : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (x v y : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (ltF v (w.relabel j)) →
      D B Δ (TickAt p other z (frameValueTerm x v y)
        (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let F := other
  have fromFrame (C : Program 3) (decode : FrameDecoder C) :
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (frame : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph C frame ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (TickAt p F z frame (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j) := by
    intro β j Δ frame keep call tick
    apply frameTransition p F C (q.relabel j) (w.relabel j) (r.relabel j)
      frame (goal.relabel j) decode call tick
    · intro Ω stay t
      exact reject β j Ω (fun f h => stay _ (keep f h)) t
    · intro γ k Ω x v y stay order next
      have all (f : Formula α) (h : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
        simpa only [formulaRelabelComposition] using stay _ (keep f h)
      have out := child γ (k ∘ j) Ω x v y all
        (by simpa only [Term.relabel_relabel] using order)
        (by simpa only [Term.relabel_relabel] using next)
      simpa only [formulaRelabelComposition] using out
  exact exact_OpenPhysicalFirstTickCases p F q w r goal
    (fun β j Δ frame keep _ call tick => fromFrame chosenFrame functionDecoder β j Δ frame keep call tick)
    root (fromFrame F otherDecodes)

/-- The actual executable first tick, with a calibrated descending
fallback available, either reaches a root terminal flag, rejects with
zero, or steps to an exact raw child with a strictly smaller witness.
No assumptions about the two program callbacks are used internally. -/
theorem exact_OpenDescendingFirstTick (p other : Program 3) (q w r : OTerm α)
    (goal : Formula α)
    (root : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (flag : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (bit rootTest ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (programGraph (rootCall p) flag ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (TickAt p (fallback other) flag z (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j))
    (reject : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (TickAt p (fallback other) z z (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j))
    (child : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (x v y : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (ltF v (w.relabel j)) →
      D B Δ (TickAt p (fallback other) z (frameValueTerm x v y)
        (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal :=
  exact_OpenDescendingFirstTickWith p (fallback other) (fallbackDecoder other) q w r goal root reject child

#print axioms exact_OpenDescendingFirstTickWith
#print axioms exact_OpenDescendingFirstTick
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingFirstTickProof
