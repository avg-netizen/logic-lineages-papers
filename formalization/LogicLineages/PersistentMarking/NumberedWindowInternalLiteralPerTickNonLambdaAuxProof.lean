module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicCoveredCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxHeaderTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDescendingTickSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoTypedAuxCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPerTickNonLambdaAuxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans sucNeZeroApply)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralAuxRootLeaf (functionLambdaHeader)
open NumberedWindowInternalLiteralAuxRootLeafFieldsProof (rawBottom exact_OpenAuxiliaryBottomEquality)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralAuxThreeWaysProof (moveAuxInputs)
open NumberedWindowInternalLiteralAuxHeaderTransportProof (exact_OpenFunctionHeaderTransport)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralDescendingTickSupportProof (frameEq)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxParentProof (exact_OpenCoveredMemoAuxParent)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRawTransport)
open NumberedWindowInternalLiteralMemoTypedAuxCasesProof (endpointGuardsRename)
open NumberedWindowInternalLiteralAtomicCoveredCasesProof
  (PerTickRaw exact_OpenAtomicCoveredChildCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual zero function-header report excludes beta. The
remaining root is exactly raw bottom at the original queried type,
or the actual function child with its typed and least reports. The
zero guard is for the reported raw representative, not a claim about
all members of an arbitrary quotient class. -/
theorem exact_OpenPerTickNonLambdaAuxiliary (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (base : Program 2) (T V : Program 1)
    (ctx ty q w r : OTerm α) (goal : Formula α)
    (aux : D B Γ (bit sourceIsAux ![q,w,r]))
    (notLambda : D B Γ (programGraph functionLambdaHeader z ![q,w,r]))
    (held : D B Γ (programGraph (PerTickRaw C s leaf other base T V) (suc z) ![ctx,ty,q,w,r]))
    (isBottom : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (r.relabel j) (rawBottom (ty.relabel j))) → D B Δ (goal.relabel j))
    (context : D B Γ (liftedEndpointGuards (coveredMemoWindow C s base T V) V ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (dom cod fn arg child dom' cod' dest arg' : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
          dom cod fn arg child dom' cod' dest arg' →
        D B Δ (programGraph (PerTickRaw C s leaf other base T V) (suc z)
          ![ctx.relabel j,rawCons dom cod,fn,child,dest] ⊓
          (childAtWindow (coveredMemoWindow C s base T V) V (ctx.relabel j) dom arg ⊓
            (hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) (rawCons dom cod) fn ⊓
              (hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) (rawCons dom cod) dest ⊓
                hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) dom arg)))) →
        D B Δ (goal.relabel j)) : D B Γ goal := by
  let W := coveredMemoWindow C s base T V
  apply exact_OpenAtomicCoveredChildCases C X s leaf other base T V ctx ty q w r goal aux held
  · intro _ β j Δ payload keep _ _ yes
    have denied := renameInto notLambda j Δ keep
    simp only [programRename,tripleInputsRename,zRelabel] at denied
    have moved := exact_OpenFunctionHeaderTransport (q.relabel j) (w.relabel j) (r.relabel j)
      payload (r.relabel j) z denied
    obtain ⟨bad⟩ := valueUnique functionLambdaHeader (suc z) z
      ![q.relabel j,payload,r.relabel j] yes moved
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro guards β j Δ payload keep _ _ reports
    let q' := q.relabel j
    let r' := r.relabel j
    have aux₁ := moveBit sourceIsAux q w r j Δ keep aux
    have aux₂ := moveAuxInputs q' (w.relabel j) r' payload r' aux₁
    apply exact_OpenAuxiliaryBottomEquality q' payload r' (goal.relabel j) aux₂ reports
    intro γ k Ω dom cod fn arg stay opened result
    let l := k ∘ j
    have both (f : Formula α) (h : f ∈ Γ) : f.relabel l ∈ Ω := by
      simpa only [l,formulaRelabelComposition] using stay _ (keep f h)
    have moved := renameInto guards l Ω both
    rw [endpointGuardsRename] at moved
    obtain ⟨hits⟩ := moved
    have source := windowRawTransport W (ctx.relabel l) (ty.relabel l) (q.relabel l)
      (NumberedWindowInternalSparseRawFunctionFrameTargets.auxiliaryTerm dom cod fn arg)
      (by simpa only [l,q',Term.relabel_relabel] using opened)
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hits)⟩
    obtain ⟨typed⟩ := exact_OpenCoveredMemoAuxParent C s base T V
      (ctx.relabel l) (ty.relabel l) dom cod fn arg source
    obtain ⟨eqType⟩ := frameEq (numeral 3) cod (ty.relabel l)
      ⟨symm (Derivation.conjunctionLeft typed)⟩
    obtain ⟨eqRaw⟩ := result
    have raw : Derivation B Ω (eqn (r.relabel l) (rawBottom cod)) := by
      simpa only [l,r',Term.relabel_relabel] using eqRaw
    have done := isBottom γ l Ω both ⟨ID1Completion.InternalTagArithmeticSupportProof.trans raw eqType⟩
    simpa only [l,formulaRelabelComposition] using done
  · exact context

#print axioms exact_OpenPerTickNonLambdaAuxiliary
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPerTickNonLambdaAuxProof
