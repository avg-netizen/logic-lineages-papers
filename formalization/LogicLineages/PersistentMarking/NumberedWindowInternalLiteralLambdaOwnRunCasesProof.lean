module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaContextOwnRunProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFrameZeroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRunTerminalFlagProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaOwnRunCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue valueUnique outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame termShape)
open NumberedWindowInternalSparseRawTick (rootTest rootCall)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralRunTerminalFlagProof (exact_OpenTerminalFirstTickFlag)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt exact_OpenPhysicalFirstTickCases)
open NumberedWindowInternalLiteralDescendingTickSupportProof (tickFrameCases tickFrame)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralAtomicFrameZeroProof (exact_OpenLiteralAtomicNoFunctionFrame)
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts)
open NumberedWindowInternalLiteralLambdaFallbackUnderlyingProof (exact_OpenLambdaRejectsAuxiliarySource)
open NumberedWindowInternalLiteralLambdaContextOwnRunProof (fullLambdaFallback exact_OpenLambdaContextOwnRun)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem actualNoAux (q w r : OTerm α) (header : D B Γ (unary cellHead (numeral 2) q)) :
    D B Γ (unary termShape z q) := by
  apply compositionRecover termShape (fun _ : Fin 1 => .projection 0) z ![q,w,r] ![q]
    (exact_OpenLambdaRejectsAuxiliarySource q w r header)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 (![q,w,r] : Fin 3 → OTerm α)

private theorem rejectZeroFrame (P F : Program 3) (q w r : OTerm α)
    (tick : D B Γ (TickAt P F z z q w r)) (accepts : D B Γ (bit (ownRun P F) ![q,w,r])) :
    D B Γ (⊥ : Formula α) := by
  obtain ⟨bad⟩ := exact_OpenTerminalFirstTickFlag P F q w r z tick accepts
  exact ⟨sucNeZeroApply (symm bad)⟩

/-- A successful original run from a genuine lambda head is either
an actual root leaf or a true tag-one contextual lambda reduction.
The latter exposes both literal lambda bodies, the common binder
and an accepting run for the exact child at its own witness. -/
theorem exact_OpenLambdaOwnRunCases (P other : Program 3) (q w r : OTerm α) (goal : Formula α)
    (header : D B Γ (unary cellHead (numeral 2) q))
    (held : D B Γ (bit (ownRun P (fullLambdaFallback other)) ![q,w,r]))
    (root : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (bit rootTest ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (bit (rootCall P) ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (goal.relabel j))
    (child : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d a inner e b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      LambdaParts B Δ (q.relabel j) (w.relabel j) (r.relabel j) d a inner e b →
      D B Δ (bit (ownRun P (fullLambdaFallback other)) ![a,inner,b]) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let F := fullLambdaFallback other
  apply exact_OpenPhysicalFirstTickCases P F q w r goal
  · intro β j Δ frame keep _ call tick
    let q' := q.relabel j
    let w' := w.relabel j
    let r' := r.relabel j
    have h := renameInto header j Δ keep
    rw [unaryRename,numeralRename] at h
    have zero := exact_OpenLiteralAtomicNoFunctionFrame q' w' r' (actualNoAux q' w' r' h)
    have eq := valueUnique chosenFrame frame z ![q',w',r'] call zero
    have off := tickFrame P F z frame z q' w' r' tick eq
    have impossible := rejectZeroFrame P F q' w' r' off (moveBit (ownRun P F) q w r j Δ keep held)
    exact impossible.map Derivation.explosion
  · intro β j Δ flag keep good call tick
    have ok := moveBit (ownRun P F) q w r j Δ keep held
    have unit := exact_OpenTerminalFirstTickFlag P F (q.relabel j) (w.relabel j) (r.relabel j) flag tick ok
    exact root β j Δ keep good (outputTransport (rootCall P) flag (suc z) ![q.relabel j,w.relabel j,r.relabel j] unit call)
  · intro β j Δ frame keep callback first
    let q' := q.relabel j
    let w' := w.relabel j
    let r' := r.relabel j
    have h := renameInto header j Δ keep
    rw [unaryRename,numeralRename] at h
    have a := moveBit (ownRun P F) q w r j Δ keep held
    apply tickFrameCases P F q' w' r' frame (goal.relabel j) first
    · intro Ω stay no
      have rejected := rejectZeroFrame P F q' w' r' no (a.map (Derivation.weakening stay))
      exact rejected.map Derivation.explosion
    · intro γ k Θ n stay eq tick
      have call' := renameInto callback k Θ stay
      rw [programRename,tripleInputsRename] at call'
      have good := outputTransport F (frame.relabel k) (suc n) ![q'.relabel k,w'.relabel k,r'.relabel k] eq call'
      have h' := renameInto h k Θ stay
      rw [unaryRename,numeralRename] at h'
      have ready := moveBit (ownRun P F) q' w' r' k Θ stay a
      apply exact_OpenLambdaContextOwnRun P other (q'.relabel k) (w'.relabel k) (r'.relabel k) n
        ((goal.relabel j).relabel k) h' tick good ready
      intro δ l Ξ d old inner e after retain row next
      let m := l ∘ k ∘ j
      have all (φ : Formula α) (hφ : φ ∈ Γ) : φ.relabel m ∈ Ξ := by
        simpa only [m,formulaRelabelComposition,Function.comp_assoc] using retain _ (stay _ (keep φ hφ))
      have out := child δ m Ξ d old inner e after all
        (by simpa only [m,q',w',r',Term.relabel_relabel,Function.comp_assoc] using row) next
      simpa only [m,formulaRelabelComposition,Function.comp_assoc] using out

#print axioms exact_OpenLambdaOwnRunCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaOwnRunCasesProof
