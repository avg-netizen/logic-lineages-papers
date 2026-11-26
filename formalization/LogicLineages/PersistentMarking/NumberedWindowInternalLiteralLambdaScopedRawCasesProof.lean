module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixScopeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaChildRawRebuildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixRawFitProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaScopedRawCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawTick (rootTest rootCall)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback)
open NumberedWindowInternalLiteralLambdaContextOwnRunProof (fullLambdaFallback)
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts)
open NumberedWindowInternalLiteralLambdaTypedRawCasesProof (exact_OpenLambdaTypedRawCases)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixScopeProof (movePrefixBit exact_OpenPrefixLexicalCases)
open NumberedWindowInternalLiteralLambdaPrefixRawFitProof (prefixRaw exact_OpenPrefixRaw)
open NumberedWindowInternalLiteralLambdaChildRawRebuildProof (exact_OpenRebuildLambdaChildRaw)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A successful checked raw step out of a lambda is either the same
original root leaf or the exact body step accepted by the original
typed checker at the pushed lexical context. The child carries its
own witness and both of the selected original window programs. -/
theorem exact_OpenScopedLambdaRawCases (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (c t q w r : OTerm α) (goal : Formula α) :
    let Q := joinedAuxiliaryWindow s base T V TV baseM
    let raw := selectedJoinedRaw s base T V TV baseM leaf (lambdaFallback other)
    let P := atomicRoot (root (leafAtAuxiliary leaf))
    D B Γ (unary cellHead (numeral 2) q) →
    D B Γ (programGraph (prefixRaw Q raw) (suc z) ![c,t,q,w,r]) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (bit rootTest ![q.relabel j,w.relabel j,r.relabel j]) →
      D B Δ (bit (rootCall P) ![q.relabel j,w.relabel j,r.relabel j]) → D B Δ (goal.relabel j)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d a inner b cod : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (t.relabel j) (rawCons d cod)) →
      D B Δ (windowAt Q (rawCons d (c.relabel j)) cod a) →
      D B Δ (windowAt Q (rawCons d (c.relabel j)) cod b) →
      D B Δ (programGraph raw (suc z) ![rawCons d (c.relabel j),cod,a,inner,b]) →
      D B Δ (programGraph (prefixTick Q) (prefixStartTerm (rawCons d (c.relabel j)) cod a inner b)
        ![prefixStartTerm (c.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)]) →
      D B Δ (goal.relabel j)) →
    D B Γ goal := by
  intro Q raw P header checked rootCase childCase
  obtain ⟨old,lex⟩ := (exact_OpenPrefixRaw Q raw ![c,t,q,w,r]).mp checked
  apply exact_OpenLambdaTypedRawCases s base T V TV baseM leaf other c t q w r goal header old
  · intro _ _
    exact rootCase
  · intro _ _ β j Δ d a inner e b keep row own
    have guard := movePrefixBit (prefixOwn Q) c t q w r j Δ keep lex
    have h := renameInto header j Δ keep
    rw [unaryRename,numeralRename] at h
    apply exact_OpenPrefixLexicalCases Q (c.relabel j) (t.relabel j) (q.relabel j)
      (w.relabel j) (r.relabel j) d a inner e b (goal.relabel j) h row guard
    intro γ k Ω cod stay arrow left right tick
    let m := k ∘ j
    have all (f : Formula α) (mem : f ∈ Γ) : f.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition,Function.comp_assoc] using stay _ (keep f mem)
    have suffix := moveBit (ownRun P (fullLambdaFallback other)) a inner b k Ω stay own
    have rawChild := exact_OpenRebuildLambdaChildRaw s base T V TV baseM leaf other
      (rawCons (d.relabel k) ((c.relabel j).relabel k)) cod (a.relabel k) (inner.relabel k) (b.relabel k)
      left right suffix
    have result := childCase γ m Ω (d.relabel k) (a.relabel k) (inner.relabel k) (b.relabel k) cod all
      (by simpa only [m,Term.relabel_relabel] using arrow)
      (by simpa only [m,Term.relabel_relabel] using left)
      (by simpa only [m,Term.relabel_relabel] using right)
      (by simpa only [m,Term.relabel_relabel] using rawChild)
      (by simpa only [m,Term.relabel_relabel] using tick)
    simpa only [m,formulaRelabelComposition,Function.comp_assoc] using result

#print axioms exact_OpenScopedLambdaRawCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaScopedRawCasesProof
