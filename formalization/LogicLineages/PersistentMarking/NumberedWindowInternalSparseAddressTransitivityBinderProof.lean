module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)

theorem suppliedEdgeRename {α β : Type} (r : Program 3) (x y : OTerm α) (j : α → β) :
    (suppliedEdge r x y).relabel j = suppliedEdge r (x.relabel j) (y.relabel j) := by
  simp only [suppliedEdge,existsRename,acceptsRename,Term.relabel_relabel,Term.relabel] <;> rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem provide (r : Program 3) (x w y : OTerm α)
    (known : Nonempty (Derivation body Γ (accepts r x w y))) :
    Nonempty (Derivation body Γ (suppliedEdge r x y)) := by
  let row := accepts r (x.relabel Sum.inl) (.var (.inr (0 : Fin 1))) (y.relabel Sum.inl)
  have h : instantiate row (emb w) = accepts r x w y := by
    simp only [row,instantiate,bindEmbedding,acceptsSubst,liftBind,varBind]
  obtain ⟨known⟩ := known
  exact ⟨Derivation.existentialIntroduction (phi := row) (emb w) (h.symm ▸ known)⟩

theorem consume (r : Program 3) (x y : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (suppliedEdge r x y)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (accepts r (x.relabel j) w (y.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨known⟩ := known
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := accepts r (x.relabel j) w (y.relabel j)
  let Δ := row :: Γ.map weaken
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  obtain ⟨result⟩ := k (α ⊕ Fin 1) j Δ w hJ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination known result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
