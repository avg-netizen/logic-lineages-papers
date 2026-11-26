module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaScopedRawCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaAddressedRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaScopedAddressedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawTick (rootTest rootCall)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback)
open NumberedWindowInternalLiteralLambdaPrefixRawFitProof (prefixRaw)
open NumberedWindowInternalLiteralLambdaAddressedRawProof (exact_OpenLambdaAddressedRaw)
open NumberedWindowInternalLiteralLambdaScopedRawCasesProof (exact_OpenScopedLambdaRawCases)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralNeutralAtomProof (lambdaHeader)
open NumberedWindowInternalNeutralFactsTargets (atom direct)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

/-- At an actual addressed quotient step from a lambda, either open the
original root certificate or obtain a typed body reduction at the
pushed context on the very same prefix-certified raw program. -/
theorem exact_OpenAddressedScopedLambdaCases (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (leaf : Nat → Program 3) (other pre : Program 3) (i cv tv : Program 1)
    (c : Nat) (x y : OTerm α) (goal : Formula α) :
    let Q := joinedAuxiliaryWindow s base T V TV baseM
    let raw := prefixRaw Q (selectedJoinedRaw s base T V TV baseM leaf (lambdaFallback other))
    let P := atomicRoot (root (leafAtAuxiliary leaf))
    let L := guardedLeast (headerLeast pre)
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let H := hop cv tv R L
    let B := sourceBody data c
    D B Γ (atom lambdaHeader x) → D B Γ (direct data H c x y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (bit rootTest ![q,w,r]) →
      D B Δ (bit (rootCall P) ![q,w,r]) → D B Δ (goal.relabel j)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ctx t w d a inner b cod : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn t (rawCons d cod)) →
      D B Δ (ltF inner w) →
      D B Δ (windowAt Q (rawCons d ctx) cod a) →
      D B Δ (windowAt Q (rawCons d ctx) cod b) →
      D B Δ (programGraph raw (suc z) ![rawCons d ctx,cod,a,inner,b]) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro Q raw P L R data H B head directStep rootCase contextual
  apply exact_OpenLambdaAddressedRaw i cv tv raw pre c x y goal head directStep
  intro β j Δ ctx ty before after cert q w r keep _ _ _ _ _ header calls
  obtain ⟨record⟩ := calls
  have checked : D B Δ (programGraph raw (suc z) ![ctx,ty,q,w,r]) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight record)⟩
  apply exact_OpenScopedLambdaRawCases s base T V TV baseM leaf other ctx ty q w r (goal.relabel j) header checked
  · intro γ k Ω stay rootTag branchCall
    let m := k ∘ j
    have all (f : Formula α) (mem : f ∈ Γ) : f.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition,Function.comp_assoc] using stay _ (keep f mem)
    have result := rootCase γ m Ω (q.relabel k) (w.relabel k) (r.relabel k) all rootTag branchCall
    simpa only [m,formulaRelabelComposition,Function.comp_assoc] using result
  · intro γ k Ω d a inner b cod stay arrow lWin rWin smaller next _
    let m := k ∘ j
    have all (f : Formula α) (mem : f ∈ Γ) : f.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition,Function.comp_assoc] using stay _ (keep f mem)
    have result := contextual γ m Ω (ctx.relabel k) (ty.relabel k) (w.relabel k) d a inner b cod
      all arrow smaller lWin rWin next
    simpa only [m,formulaRelabelComposition,Function.comp_assoc] using result

#print axioms exact_OpenAddressedScopedLambdaCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaScopedAddressedProof
