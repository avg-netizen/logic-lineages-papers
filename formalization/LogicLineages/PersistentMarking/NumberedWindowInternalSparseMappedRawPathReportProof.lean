module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMappedRawPathReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel sucSubst)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof
  (actualFiniteExistentialIntroduction actualFiniteExistentialElimination)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (positiveSubst)
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)

def leastAt {α : Type} (least : Program 3) (ctx ty raw k : OTerm α) : Formula α :=
  programGraph least (suc k) ![ctx,ty,raw]

def payload {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty l r a b cert : OTerm α) : Formula α :=
  leastAt least ctx ty l a ⊓ (leastAt least ctx ty r b ⊓ positiveAt raw least ctx ty a cert b)

def row {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty l r : OTerm α) : Formula (α ⊕ Fin 3) :=
  let j : α → α ⊕ Fin 3 := Sum.inl
  payload raw least (ctx.relabel j) (ty.relabel j) (l.relabel j) (r.relabel j)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

/-- The original output least calls share the same endpoint classes as
the accepted original composed positive certificate. -/
def mapped {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty l r : OTerm α) : Formula α :=
  block (row raw least ctx ty l r)

theorem leastRename {α β : Type} (least : Program 3) (ctx ty raw k : OTerm α) (j : α → β) :
    (leastAt least ctx ty raw k).relabel j =
      leastAt least (ctx.relabel j) (ty.relabel j) (raw.relabel j) (k.relabel j) := by
  simp only [leastAt,programRename,tripleInputsRename,sucRelabel]

theorem mappedRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty l r : OTerm α) (j : α → β) :
    (mapped raw least ctx ty l r).relabel j =
      mapped raw least (ctx.relabel j) (ty.relabel j) (l.relabel j) (r.relabel j) := by
  simp only [mapped,blockRename,row,payload,conjunctionRename,leastRename,positiveRename,
    Term.relabel_relabel,Term.relabel] <;> rfl

private theorem leastSubst {α β : Type} (least : Program 3)
    (ctx ty raw k : OTerm α) (ts : α → OTerm β) :
    (leastAt least ctx ty raw k).subst (fun a => emb (ts a)) =
      leastAt least (ctx.subst ts) (ty.subst ts) (raw.subst ts) (k.subst ts) := by
  have ht : (fun i : Fin 3 => (![ctx,ty,raw] i).subst ts) =
      (![ctx.subst ts,ty.subst ts,raw.subst ts] : Fin 3 → OTerm β) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) i
  simp only [leastAt,programSubst,sucSubst,ht]

private theorem witness {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty l r a b cert : OTerm α) :
    (row raw least ctx ty l r).subst (Sum.elim Term.var (fun i => emb (![a,b,cert] i))) =
      payload raw least ctx ty l r a b cert := by
  let xs : Fin 3 → OTerm α := ![a,b,cert]
  let ts : α ⊕ Fin 3 → OTerm α := Sum.elim Term.var xs
  have eq : (Sum.elim Term.var (fun i => emb (xs i))) = (fun x => emb (ts x)) := by
    funext x
    cases x <;> rfl
  have keep (x : OTerm α) : (x.relabel (Sum.inl : α → α ⊕ Fin 3)).subst ts = x :=
    ID1Completion.InternalRecursionGraphSyntaxProof.witnessLift x xs
  have h0 : (Term.var (.inr (0 : Fin 3)) : OTerm (α ⊕ Fin 3)).subst ts = a := rfl
  have h1 : (Term.var (.inr (1 : Fin 3)) : OTerm (α ⊕ Fin 3)).subst ts = b := rfl
  have h2 : (Term.var (.inr (2 : Fin 3)) : OTerm (α ⊕ Fin 3)).subst ts = cert := rfl
  change (row raw least ctx ty l r).subst (Sum.elim Term.var (fun i => emb (xs i))) = _
  rw [eq]
  unfold row payload
  simp only [conjunctionSubst,leastSubst,positiveSubst,keep,h0,h1,h2]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem provide (raw : Program 5) (least : Program 3) (ctx ty l r a b cert : OTerm α)
    (given : Nonempty (Derivation body Γ (payload raw least ctx ty l r a b cert))) :
    Nonempty (Derivation body Γ (mapped raw least ctx ty l r)) := by
  apply actualFiniteExistentialIntroduction body α 3 Γ (row raw least ctx ty l r)
    (fun i => emb (![a,b,cert] i))
  rw [witness]
  exact given

theorem casesMapped (raw : Program 5) (least : Program 3) (ctx ty l r : OTerm α)
    (goal : Formula α) (given : Nonempty (Derivation body Γ (mapped raw least ctx ty l r)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b cert : OTerm β),
      (∀ q ∈ Γ, q.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (payload raw least (ctx.relabel j) (ty.relabel j)
        (l.relabel j) (r.relabel j) a b cert)) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 3 := Sum.inl
  let r₀ := row raw least ctx ty l r
  let Δ := r₀ :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 3 Γ r₀ goal given
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have facts : Derivation body Δ r₀ := Derivation.hypothesis List.mem_cons_self
  exact next (α ⊕ Fin 3) j Δ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) keep ⟨facts⟩

#print axioms provide
#print axioms casesMapped
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMappedRawPathReportProof
