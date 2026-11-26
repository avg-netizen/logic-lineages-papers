module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawSuccessInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeOwnProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOwnRawSuccessProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue headTransport valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawRun (initialState iterateState ownRun)
open NumberedWindowInternalSparseRawTick (rootCall stateFrame rowSource rowWitness rowDestination)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRunSuccessProof (ownRunTerminal headRead)
open NumberedWindowInternalSparseRawRunShapeOwnProof (initialGraph)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D)
open NumberedWindowInternalLiteralRawSuccessInductionProof (exact_OpenLiteralRawSuccessElimination)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An accepted original own-witness run, even with an arbitrary open
witness, must reach a genuine root callback on an actually selected
earlier scratch. Its initialization cannot itself be a success because
the physical initial flag is exactly zero. The root tape may follow
contextual ticks; no claim of identity with the initial tape is made. -/
theorem exact_OpenLiteralOwnRawSuccessCases (p other : Program 3) (q w r k : OTerm α)
    (goal : Formula α)
    (held : D B Γ (programGraph (ownRun p other) (suc k) ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (u prev frame : OTerm β) (tape : Fin 3 → OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (programGraph (iterateState p other) prev
        ![u,(stateTerm z (frameValueTerm q w r)).relabel j]) →
      D B Δ (unary stateFrame (suc frame) prev) →
      D B Δ (unary rowSource (tape 0) prev) →
      D B Δ (unary rowWitness (tape 1) prev) →
      D B Δ (unary rowDestination (tape 2) prev) →
      D B Δ (programGraph (rootCall p) (suc (k.relabel j)) tape) →
      D B Δ (goal.relabel j)) :
    D B Γ goal := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let start := stateTerm z (frameValueTerm q w r)
  let out := stateTerm (suc k) z
  have terminal := ownRunTerminal p other k xs held
  have run : D B Γ (programGraph (iterateState p other) out ![w,start]) := by
    apply compositionRecover (iterateState p other) ![.projection 1,initialState] out xs ![w,start] terminal
    intro i
    exact Fin.cases (projectionValue 1 xs) (Fin.cases (initialGraph xs) (fun e => Fin.elim0 e)) i
  apply exact_OpenLiteralRawSuccessElimination p other w start k z goal run _ use
  intro Δ _ same
  have init : D B Δ (programGraph cellHead z ![start]) := headRead z (frameValueTerm q w r)
  have zero := headTransport cellHead z start out ![] same init
  obtain ⟨bad⟩ := valueUnique cellHead (suc k) z ![out] (headRead (suc k) z) zero
  exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

#print axioms exact_OpenLiteralOwnRawSuccessCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOwnRawSuccessProof
