module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind sucSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)

abbrev binder (ctx ty seed : OTerm α) : Formula (α ⊕ Fin 1) :=
  leastGraph C X W s (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (seed.relabel Sum.inl) (.var (.inr 0))

theorem hasRename {β : Type} (ctx ty seed : OTerm α) (j : α → β) :
    (hasLeast C X W s ctx ty seed).relabel j = hasLeast C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  unfold hasLeast
  rw [existsRename,leastRename]
  simp only [Term.relabel_relabel]
  rfl

private theorem leastSubst {β : Type} (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (leastGraph C X W s ctx ty seed x).subst (fun a => emb (ts a)) =
    leastGraph C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  have tape : (fun i => ((![ctx,ty,seed] : Fin 3 → OTerm α) i).subst ts) = ![ctx.subst ts,ty.subst ts,seed.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [leastGraph,programSubst,sucSubst,tape]

theorem enter (ctx ty seed x : OTerm α) (d : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed x))) :
    Nonempty (Derivation body Γ (hasLeast C X W s ctx ty seed)) := by
  obtain ⟨d⟩ := d
  change Nonempty (Derivation body Γ (existsOne (binder C X W s ctx ty seed)))
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb x)
  simpa only [instantiate,binder,bindEmbedding,leastSubst,liftBind,varBind] using d

theorem casesLeast (ctx ty seed : OTerm α) (goal : Formula α)
    (input : Nonempty (Derivation body Γ (hasLeast C X W s ctx ty seed)))
    (finish : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (leastGraph C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j) x)) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  obtain ⟨d⟩ := input
  let Δ := binder C X W s ctx ty seed :: Γ.map weaken
  obtain ⟨done⟩ := finish (α ⊕ Fin 1) Sum.inl Δ (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination d done⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
