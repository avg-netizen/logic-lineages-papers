module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (finishSubst)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowSubst)
open NumberedWindowInternalSparseFieldInductionTargets (atCode atIndex)

def safe (raw : Program 5) (least W : Program 3) {α : Type} (ctx ty cert target : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((windowAt W (ctx.relabel j) (ty.relabel j) x ⊓
    finishAt raw least (ctx.relabel j) (ty.relabel j) x (cert.relabel j) (target.relabel j)).imp
      (windowAt W (ctx.relabel j) (ty.relabel j) (target.relabel j)))

theorem safeSubst {α β : Type} (raw : Program 5) (least W : Program 3) (ctx ty cert target : OTerm α)
    (ts : α → OTerm β) : (safe raw least W ctx ty cert target).subst (fun a => emb (ts a)) =
      safe raw least W (ctx.subst ts) (ty.subst ts) (cert.subst ts) (target.subst ts) := by
  simp only [safe,allEmbeddedSubst,impSubst,conjunctionSubst,windowSubst,finishSubst,liftTermSubst]
  rfl

theorem safeRename {α β : Type} (raw : Program 5) (least W : Program 3) (ctx ty cert target : OTerm α)
    (j : α → β) : (safe raw least W ctx ty cert target).relabel j =
      safe raw least W (ctx.relabel j) (ty.relabel j) (cert.relabel j) (target.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (safe raw least W ctx ty cert target).subst (fun a => emb (.var (j a))) = _
  rw [safeSubst]
  simp only [termRelabelAsSubst]

def motive {α : Type} (raw : Program 5) (least W : Program 3) (ctx ty target : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  safe raw least W (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 0)) (target.relabel Sum.inl)

theorem motiveAt {α : Type} (raw : Program 5) (least W : Program 3) (ctx ty cert target : OTerm α) :
    atCode (motive raw least W ctx ty target) cert = safe raw least W ctx ty cert target := by
  simp only [atCode,motive,instantiate,bindEmbedding,safeSubst,liftBind,varBind]

theorem motiveIndex {α : Type} (raw : Program 5) (least W : Program 3) (ctx ty target : OTerm α)
    (i : Fin 3) : atIndex (motive raw least W ctx ty target) i =
      safe raw least W (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr i)) (target.relabel Sum.inl) := by
  unfold atIndex motive
  rw [safeRename]
  simp only [Term.relabel_relabel] <;> rfl

theorem applyAt {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least W : Program 3) (ctx ty source cert target : OTerm α)
    (known : Nonempty (Derivation body Γ (safe raw least W ctx ty cert target))) :
    Nonempty (Derivation body Γ ((windowAt W ctx ty source ⊓ finishAt raw least ctx ty source cert target).imp
      (windowAt W ctx ty target))) := by
  obtain ⟨d⟩ := known
  have law := Derivation.universalElimination (emb source) d
  simpa only [instantiate,bindEmbedding,impSubst,conjunctionSubst,windowSubst,finishSubst,liftBind,varBind]
    using (Nonempty.intro law)

theorem introduce {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least W : Program 3) (ctx ty cert target : OTerm α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (windowAt W (ctx.relabel j) (ty.relabel j) x)) →
      Nonempty (Derivation body Δ (finishAt raw least (ctx.relabel j) (ty.relabel j) x (cert.relabel j) (target.relabel j))) →
      Nonempty (Derivation body Δ (windowAt W (ctx.relabel j) (ty.relabel j) (target.relabel j)))) :
    Nonempty (Derivation body Γ (safe raw least W ctx ty cert target)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := windowAt W (ctx.relabel j) (ty.relabel j) x ⊓
    finishAt raw least (ctx.relabel j) (ty.relabel j) x (cert.relabel j) (target.relabel j)
  let Δ := A :: Γ.map weaken
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := each _ j Δ x (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowMotiveProof
