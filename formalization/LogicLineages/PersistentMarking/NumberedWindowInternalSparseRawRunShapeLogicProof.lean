module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeLogicProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (liftTerms liftTermSubst existsEmbeddedSubst)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding bindTerm varBind)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (shapeCore goodUnfold coreSubst)

theorem goodSubst {α β : Type} (out : OTerm α) (ts : α → OTerm β) :
    (goodState out).subst (fun a => emb (ts a)) = goodState (out.subst ts) := by
  rw [goodUnfold,goodUnfold,existsEmbeddedSubst,existsEmbeddedSubst,coreSubst,
    liftTermSubst,liftTermSubst]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The shape is a formula of its term: ordinary equality elimination. -/
theorem goodTransport (a b : OTerm α)
    (he : Nonempty (Derivation body Γ (eqn a b)))
    (hg : Nonempty (Derivation body Γ (goodState a))) :
    Nonempty (Derivation body Γ (goodState b)) := by
  let theta : Formula (α ⊕ Fin 1) := goodState (.var (.inr 0))
  have inst (t : OTerm α) : instantiate theta (emb t) = goodState t := by
    simp only [theta,instantiate,bindEmbedding,goodSubst,varBind]
  obtain ⟨de⟩ := he
  obtain ⟨dg⟩ := hg
  have h := Derivation.equalityElimination theta (emb a) (emb b) de (by rw [inst]; exact dg)
  rw [inst] at h
  exact ⟨h⟩

/-- Eliminate both literal quantifiers: flag and frame become object
eigenvariables carrying the actual scratch equation and zero disjunct. -/
theorem goodCases (Γ : List (Formula α)) (out : OTerm α) (ψ : Formula α)
    (h : Nonempty (Derivation body Γ (goodState out)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (f F : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (eqn (out.relabel j) (stateTerm f F))) →
      Nonempty (Derivation body Δ (eqn f z ⊔ eqn F z)) →
      Nonempty (Derivation body Δ (ψ.relabel j))) :
    Nonempty (Derivation body Γ ψ) := by
  obtain ⟨h⟩ := h
  let j : α → (α ⊕ Fin 1) ⊕ Fin 1 := fun a => .inl (.inl a)
  let f : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
  let F : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let A : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    shapeCore ((out.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl) f F
  let Δ : List (Formula ((α ⊕ Fin 1) ⊕ Fin 1)) :=
    A :: (existsOne A :: Γ.map weaken).map weaken
  have h2 : Derivation body Γ (existsOne (existsOne A)) := by
    rw [goodUnfold] at h
    exact h
  have core : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have hout : (out.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl = out.relabel j := by
    rw [Term.relabel_relabel]
    rfl
  have twice (φ : Formula α) : φ.relabel j = weaken (weaken φ) := by
    unfold weaken
    rw [formulaRelabelComposition]
    rfl
  have he : Nonempty (Derivation body Δ (eqn (out.relabel j) (stateTerm f F))) := by
    rw [← hout]
    exact ⟨Derivation.conjunctionLeft core⟩
  have hz : Nonempty (Derivation body Δ (eqn f z ⊔ eqn F z)) :=
    ⟨Derivation.conjunctionRight core⟩
  have hmem : ∀ φ ∈ Γ, φ.relabel j ∈ Δ := by
    intro φ hφ
    rw [twice]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨weaken φ,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,hφ,rfl⟩),rfl⟩)
  obtain ⟨d⟩ := k _ j Δ f F hmem he hz
  rw [twice] at d
  exact ⟨Derivation.existentialElimination h2
    (Derivation.existentialElimination (Derivation.hypothesis List.mem_cons_self) d)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeLogicProof
