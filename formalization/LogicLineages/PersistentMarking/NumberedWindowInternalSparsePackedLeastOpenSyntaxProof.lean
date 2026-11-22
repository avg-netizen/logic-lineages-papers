module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding bindTerm liftBind varBind sucRelabel sucSubst zSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (liftTerms liftTermSubst existsEmbeddedSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen

attribute [local irreducible] programGraph

/-- The literal matrix under both object quantifiers of `poolOccurrence`:
context payload is the outer bound variable, pool the inner one. -/
abbrev binder {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α) : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
  poolOccurrenceRow C X W s
    ((ctx.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    ((ty.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    ((seed.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    ((selected.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl)
    (.var (.inl (.inr 0))) (.var (.inr 0))

theorem occurrenceUnfold {α : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected : OTerm α) :
    poolOccurrence C X W s ctx ty seed selected =
      existsOne (existsOne (binder C X W s ctx ty seed selected)) := rfl

private theorem tapeSubst {α β : Type} (a b c : OTerm α) (ts : α → OTerm β) :
    (fun i => ((![a,b,c] : Fin 3 → OTerm α) i).subst ts) =
      ![a.subst ts,b.subst ts,c.subst ts] := by
  funext i
  refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y =>
    Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) y) x) i <;> rfl

private theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) =
      memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

theorem leastRename {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected : OTerm α) (j : α → β) :
    (leastGraph C X W s ctx ty seed selected).relabel j =
      leastGraph C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
        (selected.relabel j) := by
  simp only [leastGraph,programRename,sucRelabel,tripleInputsRename]

private theorem rowRename {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected payload pool : OTerm α) (j : α → β) :
    (poolOccurrenceRow C X W s ctx ty seed selected payload pool).relabel j =
      poolOccurrenceRow C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
        (selected.relabel j) (payload.relabel j) (pool.relabel j) := by
  simp only [poolOccurrenceRow,conjunctionRename,programRename,sucRelabel,tripleInputsRename,
    graphRename]

private theorem rowSubst {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected payload pool : OTerm α) (ts : α → OTerm β) :
    (poolOccurrenceRow C X W s ctx ty seed selected payload pool).subst (fun a => emb (ts a)) =
      poolOccurrenceRow C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts)
        (selected.subst ts) (payload.subst ts) (pool.subst ts) := by
  simp only [poolOccurrenceRow,conjunctionSubst,programSubst,tapeSubst,sucSubst,memberSubst]

/-- Renaming the free names commutes with both binders; the two bound
variables are fixed and the lifted free terms cannot be captured. -/
theorem occurrenceRename {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (ctx ty seed selected : OTerm α) (j : α → β) :
    (poolOccurrence C X W s ctx ty seed selected).relabel j =
      poolOccurrence C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
        (selected.relabel j) := by
  rw [occurrenceUnfold,occurrenceUnfold,existsRename,existsRename]
  unfold binder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

/-- Introduce both literal quantifiers at explicit object witnesses:
first the context payload, then the pool, from the actual row. -/
theorem occurrenceIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected payload pool : OTerm α)
    (row : Nonempty (Derivation body Γ
      (poolOccurrenceRow C X W s ctx ty seed selected payload pool))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  let c' : OTerm (α ⊕ Fin 1) := ctx.relabel Sum.inl
  let t' : OTerm (α ⊕ Fin 1) := ty.relabel Sum.inl
  let q' : OTerm (α ⊕ Fin 1) := seed.relabel Sum.inl
  let k' : OTerm (α ⊕ Fin 1) := selected.relabel Sum.inl
  let p' : OTerm (α ⊕ Fin 1) := payload.relabel Sum.inl
  let A : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    poolOccurrenceRow C X W s (c'.relabel Sum.inl) (t'.relabel Sum.inl) (q'.relabel Sum.inl)
      (k'.relabel Sum.inl) (.var (.inl (.inr 0))) (.var (.inr 0))
  let B : Formula (α ⊕ Fin 1) :=
    poolOccurrenceRow C X W s c' t' q' k' p' (.var (.inr 0))
  have firstSlot :
      (Term.var (.inl (.inr 0)) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)).subst
        (liftTerms (bindTerm payload)) = p' := rfl
  have lastSlot :
      (Term.var (.inr 0) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)).subst
        (liftTerms (bindTerm payload)) =
        (Term.var (.inr 0) : OTerm (α ⊕ Fin 1)) := rfl
  have ho : instantiate (existsOne A) (emb payload) = existsOne B := by
    simp only [instantiate,bindEmbedding,existsEmbeddedSubst,A,B,rowSubst,liftTermSubst,
      c',t',q',k',liftBind,firstSlot,lastSlot]
  have hi : instantiate B (emb pool) =
      poolOccurrenceRow C X W s ctx ty seed selected payload pool := by
    simp only [instantiate,bindEmbedding,B,c',t',q',k',p',rowSubst,liftBind,varBind]
  obtain ⟨d⟩ := row
  change Nonempty (Derivation body Γ (existsOne (existsOne A)))
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb payload)
  rw [ho]
  apply Derivation.existentialIntroduction (emb pool)
  rw [hi]
  exact d

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
