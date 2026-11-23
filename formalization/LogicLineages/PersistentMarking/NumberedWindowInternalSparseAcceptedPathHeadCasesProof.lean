module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAcceptedHopCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAcceptedPathHeadCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc hopCertified)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open NumberedWindowInternalSparsePositiveHeadDecompositionChecks (exact_OpenPositiveHeadDecomposition)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (finishAtRename)
open NumberedWindowInternalSparseAcceptedHopCasesProof (advanceCases)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Genuine head/tail opening of one original certified positive path.
The continuation sees the original head and raw residual suffix,
the actual first raw child with its two least fields, and the exact
still-held suffix finish (nil is permitted). -/
theorem headCases (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (goal : Formula α)
    (live : Nonempty (Derivation body Γ (positiveAt raw least ctx ty source cert target)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (head tail middle q w r : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (consGraph (cert.relabel j) head tail)) →
      Nonempty (Derivation body Δ (hopCertified head middle q w r)) →
      Nonempty (Derivation body Δ (actualCalls raw least (ctx.relabel j) (ty.relabel j)
        (source.relabel j) middle q w r)) →
      Nonempty (Derivation body Δ (finishAt raw least (ctx.relabel j) (ty.relabel j)
        middle tail (target.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨eqv⟩ := exact_OpenPositiveHeadDecomposition body raw least α ctx ty source cert target
  obtain ⟨h⟩ := live
  have held : Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (weakenClosed eqv Γ)) h⟩
  let j : α → α ⊕ Fin 3 := Sum.inl
  let row := headRow raw least ctx ty source cert target
  let Δ := row :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 3 Γ row goal held
  let head : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let mid : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  have facts : Derivation body Δ (headData raw least (ctx.relabel j) (ty.relabel j)
      (source.relabel j) (cert.relabel j) (target.relabel j) head tail mid) :=
    Derivation.hypothesis List.mem_cons_self
  have old : ∀ p ∈ Γ, p.relabel j ∈ Δ :=
    fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩)
  have cell : Nonempty (Derivation body Δ (consGraph (cert.relabel j) head tail)) :=
    ⟨Derivation.conjunctionLeft facts⟩
  have suffix : Nonempty (Derivation body Δ (finishAt raw least (ctx.relabel j) (ty.relabel j)
      mid tail (target.relabel j))) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight facts)⟩
  obtain ⟨done⟩ := advanceCases raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) head mid
    (goal.relabel j) ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight facts)⟩
    (fun β k Θ q w r keep envelope rawStep => by
      have he := renameInto cell k Θ keep
      rw [consGraphRename] at he
      have later := renameInto suffix k Θ keep
      rw [finishAtRename] at later
      have both : ∀ p ∈ Γ, p.relabel (k ∘ j) ∈ Θ := by
        intro p hp
        simpa only [formulaRelabelComposition] using keep (p.relabel j) (old p hp)
      have result := next β (k ∘ j) Θ (head.relabel k) (tail.relabel k) (mid.relabel k)
        q w r both
        (by simpa only [Term.relabel_relabel] using he)
        envelope
        (by simpa only [Term.relabel_relabel] using rawStep)
        (by simpa only [Term.relabel_relabel] using later)
      simpa only [formulaRelabelComposition] using result)
  exact ⟨done⟩

#print axioms headCases
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAcceptedPathHeadCasesProof
