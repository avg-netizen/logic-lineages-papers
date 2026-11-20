module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst zSubst bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (positive finish)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs)
open NumberedWindowInternalSparsePositiveIterationBindingProof (loopArgsSubst)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt finishAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof (graph4Subst)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveTransitivityTargets

attribute [local irreducible] programGraph positive finish

theorem positiveSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source code target : OTerm α) (ts : α → OTerm β) :
    (positiveAt raw least ctx ty source code target).subst (fun a => emb (ts a)) =
      positiveAt raw least (ctx.subst ts) (ty.subst ts) (source.subst ts) (code.subst ts) (target.subst ts) := by
  unfold positiveAt
  change (programGraph (positive raw least) (suc z) (loopArgs ctx ty source code target)).subst
    (fun a => emb (ts a)) = _
  rw [programSubst,loopArgsSubst,sucSubst,zSubst] <;> rfl

theorem finishSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source code target : OTerm α) (ts : α → OTerm β) :
    (finishAt raw least ctx ty source code target).subst (fun a => emb (ts a)) =
      finishAt raw least (ctx.subst ts) (ty.subst ts) (source.subst ts) (code.subst ts) (target.subst ts) := by
  unfold finishAt
  rw [graph4Subst] <;> simp only [sucSubst]

theorem suppliedRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source target : OTerm α) (j : α → β) :
    (supplied raw least ctx ty source target).relabel j =
      supplied raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (target.relabel j) := by
  simp only [supplied,existsRename,positiveRename,Term.relabel_relabel,Term.relabel] <;> rfl

theorem suppliedSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source target : OTerm α) (ts : α → OTerm β) :
    (supplied raw least ctx ty source target).subst (fun a => emb (ts a)) =
      supplied raw least (ctx.subst ts) (ty.subst ts) (source.subst ts) (target.subst ts) := by
  unfold supplied
  rw [existsSubst,liftedEmbedding,positiveSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem provide {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source target code : OTerm α)
    (known : Nonempty (Derivation body Γ (positiveAt raw least ctx ty source code target))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let row := positiveAt raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (.var (.inr 0)) (target.relabel j)
  have h : instantiate row (emb code) = positiveAt raw least ctx ty source code target := by
    simp only [row,j,instantiate,bindEmbedding,positiveSubst,liftBind,varBind]
  obtain ⟨known⟩ := known
  exact ⟨Derivation.existentialIntroduction (phi := row) (emb code) (h.symm ▸ known)⟩

theorem suppliedCases {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty source target : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (supplied raw least ctx ty source target)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (code : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (positiveAt raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
        code (target.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨known⟩ := known
  let j : α → α ⊕ Fin 1 := Sum.inl
  let code : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := positiveAt raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) code (target.relabel j)
  let Δ := row :: Γ.map weaken
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  obtain ⟨result⟩ := k (α ⊕ Fin 1) j Δ code hJ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination known result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
