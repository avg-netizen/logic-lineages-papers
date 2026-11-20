module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (liftedEmbedding)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind zRelabel zSubst)
open SourceComputabilityFormulaSupportProof (existsOne)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparsePositiveTerminalityTargets

attribute [local irreducible] programGraph

private theorem pairSubst {α β : Type} (c current : OTerm α) (ts : α → OTerm β) :
    (fun i => ((![c,current] : Fin 2 → OTerm α) i).subst ts) =
      (![c.subst ts,current.subst ts] : Fin 2 → OTerm β) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> rfl

theorem scratchSubst {α β : Type} (o c current : OTerm α) (ts : α → OTerm β) :
    (scratchGraph o c current).subst (fun a => emb (ts a)) =
      scratchGraph (o.subst ts) (c.subst ts) (current.subst ts) := by
  unfold scratchGraph
  rw [programSubst,pairSubst] <;> rfl

theorem terminalRename {α β : Type} (out : OTerm α) (j : α → β) :
    (terminalScratch out).relabel j = terminalScratch (out.relabel j) := by
  unfold terminalScratch
  rw [existsRename,scratchRename,zRelabel]
  simp only [Term.relabel_relabel]
  rfl

theorem terminalSubst {α β : Type} (out : OTerm α) (ts : α → OTerm β) :
    (terminalScratch out).subst (fun a => emb (ts a)) = terminalScratch (out.subst ts) := by
  unfold terminalScratch
  rw [existsSubst,liftedEmbedding,scratchSubst]
  simp only [liftSubst,zSubst,Term.subst,Sum.elim_inr]

theorem supplyTerminal {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (out current : OTerm α)
    (known : Nonempty (Derivation body Γ (scratchGraph out z current))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  let row : Formula (α ⊕ Fin 1) := scratchGraph (out.relabel Sum.inl) z (.var (.inr 0))
  have h : instantiate row (emb current) = scratchGraph out z current := by
    simp only [row,instantiate,bindEmbedding,scratchSubst,liftBind,zSubst,varBind]
  obtain ⟨d⟩ := known
  exact ⟨Derivation.existentialIntroduction (phi := row) (emb current) (h.symm ▸ d)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof
