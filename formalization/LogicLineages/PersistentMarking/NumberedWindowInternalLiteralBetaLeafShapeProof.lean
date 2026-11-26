module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (guard)
open NumberedWindowInternalLiteralAuxRootLeafFieldsProof (sourceParts)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases moveBit)
open NumberedWindowInternalLiteralBetaLeafProof
open NumberedWindowInternalLiteralBetaLeafOpenProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveBetaCalls {β : Type} (U : Program 2) (q w r : OTerm α) (j : α → β)
    (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) (h : BetaCalls B Γ U q w r) :
    BetaCalls B Δ U (q.relabel j) (w.relabel j) (r.relabel j) :=
  ⟨moveBit _ q w r j Δ keep h.source, moveBit _ q w r j Δ keep h.functionShape,
    moveBit _ q w r j Δ keep h.domainMatch, moveBit _ q w r j Δ keep h.targetMatch⟩

/-- An actual successful replacement beta leaf reveals the actual input
lambda, its binder and body, the checked raw argument, and the very same
discharged instance carried by the certified target. -/
theorem exact_OpenLiteralBetaLeafShape (V : Program 1) (U : Program 2) (q w r : OTerm α) (goal : Formula α)
    (held : D B Γ (bit (literalBetaLeaf V U) ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dom cod fn arg bind body : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (q.relabel j) (auxiliaryTerm dom cod fn arg)) →
      D B Δ (eqn fn (rawLambdaTerm bind body)) → D B Δ (eqn dom bind) →
      D B Δ (programGraph U (suc (r.relabel j)) ![arg,body]) → D B Δ (goal.relabel j)) :
    D B Γ goal := by
  have facts := exact_OpenLiteralBetaCalls V U q w r held
  apply sourceParts q w r goal facts.source
  intro β j Δ dom cod fn arg keep eq fields
  let q₁ := q.relabel j
  let w₁ := w.relabel j
  let r₁ := r.relabel j
  let xs : Fin 3 → OTerm β := ![q₁,w₁,r₁]
  have chosen := moveBetaCalls U q w r j Δ keep facts
  have fnGraph : D B Δ (programGraph rawFunction fn xs) := onTape (field 2) 0 fn xs fields.2.2.1
  have shape : D B Δ (unary rawLambdaShape (suc z) fn) := by
    apply compositionRecover rawLambdaShape (fun _ : Fin 1 => rawFunction) (suc z) xs ![fn] chosen.functionShape
    intro i
    obtain rfl := Fin.eq_zero i
    exact fnGraph
  have lambda : D B Δ (bit (onRaw rawLambdaShape 0) ![fn,fn,fn]) :=
    onTape rawLambdaShape 0 (suc z) ![fn,fn,fn] shape
  apply nodeAtCases 2 2 0 ![fn,fn,fn] (goal.relabel j) lambda
  intro γ k Θ terms stay size lam bindings
  rcases terms with _ | ⟨d,_ | ⟨body,_ | ⟨x,more⟩⟩⟩ <;> simp at size
  let m := k ∘ j
  have combined (f : Formula α) (hf : f ∈ Γ) : f.relabel m ∈ Θ := by
    simpa only [m,formulaRelabelComposition] using stay _ (keep f hf)
  have all := moveBetaCalls U q₁ w₁ r₁ k Θ stay chosen
  have src := renameInto eq k Θ stay
  rw [eqnRelabel,auxiliaryRename] at src
  have a := renameInto fields.2.2.2.1 k Θ stay
  have f := renameInto fields.2.2.1 k Θ stay
  have d₀ := renameInto fields.1 k Θ stay
  simp only [unaryRename] at d₀ f a
  obtain ⟨same,run⟩ := exact_OpenBetaInstanceFromSelectors U (q₁.relabel k) (w₁.relabel k) (r₁.relabel k)
    (dom.relabel k) (fn.relabel k) (arg.relabel k) d body all d₀ f a bindings.1 bindings.2.1
  have out := use γ m Θ (dom.relabel k) (cod.relabel k) (fn.relabel k) (arg.relabel k) d body combined
    (by simpa only [m,q₁,Term.relabel_relabel] using src) lam same
    (by simpa only [m,r₁,Term.relabel_relabel] using run)
  simpa only [m,formulaRelabelComposition] using out

/-- Same open conclusion for the actual arity-checked replacement root
leaf used in the installed eight-way dispatcher. -/
theorem exact_OpenInstalledBetaLeafShape (V : Program 1) (U : Program 2) (leaf : Nat → Program 3)
    (q w r : OTerm α) (goal : Formula α)
    (held : D B Γ (bit (withBetaLeaf V U leaf 6) ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dom cod fn arg bind body : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (q.relabel j) (auxiliaryTerm dom cod fn arg)) →
      D B Δ (eqn fn (rawLambdaTerm bind body)) → D B Δ (eqn dom bind) →
      D B Δ (programGraph U (suc (r.relabel j)) ![arg,body]) → D B Δ (goal.relabel j)) :
    D B Γ goal := by
  simp only [withBetaLeaf,if_pos rfl] at held
  obtain ⟨checked⟩ := conjunctionRecover (guard 6 0) (literalBetaLeaf V U) ![q,w,r] held
  exact exact_OpenLiteralBetaLeafShape V U q w r goal ⟨Derivation.conjunctionRight checked⟩ use

#print axioms exact_OpenLiteralBetaLeafShape
#print axioms exact_OpenInstalledBetaLeafShape
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafShapeProof
