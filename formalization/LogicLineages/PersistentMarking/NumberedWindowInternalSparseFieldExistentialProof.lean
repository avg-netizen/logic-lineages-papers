module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionClosureSyntaxProof (liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open NumberedWindowInternalSparseFieldInductionTargets

theorem consGraphRename {α β : Type} (n x y : OTerm α) (j : α → β) :
    (consGraph n x y).relabel j = consGraph (n.relabel j) (x.relabel j) (y.relabel j) := by
  unfold consGraph
  rw [programRename]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

theorem consGraphSubst {α β : Type} (n x y : OTerm α) (ts : α → OTerm β) :
    (consGraph n x y).subst (fun a => emb (ts a)) =
      consGraph (n.subst ts) (x.subst ts) (y.subst ts) := by
  unfold consGraph programGraph
  rw [graphSubst]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

private theorem someTailRename {α β : Type} (n h : OTerm α) (j : α → β) :
    (someTail n h).relabel j = someTail (n.relabel j) (h.relabel j) := by
  simp only [someTail,existsRename,consGraphRename,Term.relabel_relabel,Term.relabel] <;> rfl

theorem someConsRename {α β : Type} (n : OTerm α) (j : α → β) :
    (someCons n).relabel j = someCons (n.relabel j) := by
  simp only [someCons,existsRename,someTailRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem someTailSubst {α β : Type} (n h : OTerm α) (ts : α → OTerm β) :
    (someTail n h).subst (fun a => emb (ts a)) = someTail (n.subst ts) (h.subst ts) := by
  unfold someTail
  rw [existsSubst,liftedEmbedding,consGraphSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem someConsSubst {α β : Type} (n : OTerm α) (ts : α → OTerm β) :
    (someCons n).subst (fun a => emb (ts a)) = someCons (n.subst ts) := by
  unfold someCons
  rw [existsSubst,liftedEmbedding,someTailSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

/-- Eliminate the genuine two nested witnesses from the original sparse cons graph. -/
theorem someConsCases {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (n : OTerm α) (ψ : Formula α)
    (h : Nonempty (Derivation body Γ (someCons n)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (hd tl : OTerm β),
      (∀ a ∈ Γ, a.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (consGraph (n.relabel j) hd tl)) →
      Nonempty (Derivation body Δ (ψ.relabel j))) :
    Nonempty (Derivation body Γ ψ) := by
  obtain ⟨h⟩ := h
  let L : α → α ⊕ Fin 1 := Sum.inl
  let R : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let y : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let A := someTail (n.relabel L) x
  let Δ := A :: Γ.map weaken
  let B := consGraph ((n.relabel L).relabel R) (x.relabel R) y
  let Θ := B :: Δ.map weaken
  have transfer : ∀ a ∈ Γ, a.relabel (R ∘ L) ∈ Θ := by
    intro p hp
    rw [← formulaRelabelComposition L R p]
    apply List.mem_cons_of_mem
    refine List.mem_map.mpr ⟨p.relabel L, ?_, rfl⟩
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hit : Nonempty (Derivation body Θ (consGraph (n.relabel (R ∘ L)) (x.relabel R) y)) := by
    rw [← Term.relabel_relabel]
    exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨done⟩ := k _ (R ∘ L) Θ (x.relabel R) y transfer hit
  rw [← formulaRelabelComposition L R ψ] at done
  have second : Derivation body Δ (weaken ψ) :=
    Derivation.existentialElimination
      (show Derivation body Δ A from Derivation.hypothesis List.mem_cons_self) done
  exact ⟨Derivation.existentialElimination h second⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
